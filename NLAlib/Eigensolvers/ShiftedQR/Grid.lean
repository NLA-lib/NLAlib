/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Blas.Pair
public import NLAlib.Ops.Logic.IndexBlock
public import NLAlib.Ops.Logic.Allocation
public import NLAlib.Matrix.QRIteration.Strategy

/-!
# Actual scalar points of the exceptional square grid

A point reads its complex center and real radius. Counted dimension-literal calls store the
two coordinates, grid denominator, and constants one and two; ten scalar arithmetic calls
then form the complex point. Both radius products are retained before the two output words
are written. The scoped version shares the same code and releases its nine scratch words.

## Main results

* `NLAlib.ShiftedQR.gridPointWithScratch`: counted literals and actual scalar grid arithmetic.
* `NLAlib.ShiftedQR.gridPointWithScratch_writes`: total exact point computation.
* `NLAlib.ShiftedQR.gridPoint`: scoped scratch version of the point program.
* `NLAlib.ShiftedQR.squareGrid_eq_gridPoints`: outer-coordinate then inner-coordinate order.
-/

@[expose] public section

namespace NLAlib.ShiftedQR

open Ops

/-- The mathematical point of the square grid with denominator `D` and coordinates `i,j`. -/
noncomputable def gridPointValue (center : ℂ) (radius : ℝ) (D i j : ℕ) : ℂ :=
  center + (radius : ℂ) * ⟨2 * (i : ℝ) / (D : ℝ) - 1, 2 * (j : ℝ) / (D : ℝ) - 1⟩

/-- The order visited by nested loops with the first coordinate outermost. -/
noncomputable def gridPoints (center : ℂ) (radius : ℝ) (D : ℕ) : List ℂ :=
  (List.range (D + 1)).flatMap fun i =>
    (List.range (D + 1)).map fun j => gridPointValue center radius D i j

/-- The nested loop order is exactly the exceptional square-grid enumeration, with the
existing ceiling denominator and its endpoint included in both coordinates. -/
theorem squareGrid_eq_gridPoints (center : ℂ) (radius ε : ℝ) :
    squareGrid center radius ε = gridPoints center radius ⌈Real.sqrt 2 / ε⌉₊ := rfl

/-- Scratch-relative address of a point computation word. -/
def gridScratch (k : ℕ) : Operand := ⟨2, .var 5 + .const k⟩

/-- The five counted dimension literals, including the two fixed arithmetic constants. -/
def gridLiterals : List (IExp × Operand) :=
  [(.var 1, gridScratch 0), (.var 2, gridScratch 1), (.var 0, gridScratch 2),
   (.const 1, gridScratch 3), (.const 2, gridScratch 4)]

/-- Ten ordinary scalar calls compute both scaled coordinates and the two point components. -/
def gridInstructions : List (ScalarIns ScalarOp) :=
  [⟨.mul, [gridScratch 4, gridScratch 0], gridScratch 5⟩,
   ⟨.div, [gridScratch 5, gridScratch 2], gridScratch 5⟩,
   ⟨.sub, [gridScratch 5, gridScratch 3], gridScratch 5⟩,
   ⟨.mul, [gridScratch 4, gridScratch 1], gridScratch 6⟩,
   ⟨.div, [gridScratch 6, gridScratch 2], gridScratch 6⟩,
   ⟨.sub, [gridScratch 6, gridScratch 3], gridScratch 6⟩,
   ⟨.mul, [⟨1, .var 4⟩, gridScratch 5], gridScratch 7⟩,
   ⟨.mul, [⟨1, .var 4⟩, gridScratch 6], gridScratch 8⟩,
   ⟨.add, [⟨0, .var 3⟩, gridScratch 7], ⟨3, .var 6⟩⟩,
   ⟨.add, [⟨0, .var 3 + .const 1⟩, gridScratch 8], ⟨3, .var 6 + .const 1⟩⟩]

variable {Op Tst : Type} [Has ScalarOp Op] [Has IndexOp Op]

/-- Compute one exceptional grid point from actual center and radius words, with nine
caller-owned scratch words. Dimensions are denominator, first coordinate, second coordinate. -/
def gridPointWithScratch : Impl Op Tst :=
  ⟨3, 3, 1, .seq (.indexBlock gridLiterals)
    (.scalarBlock (gridInstructions.map ScalarIns.lift))⟩

/-- Compute one exceptional grid point with nine scoped scratch words. -/
def gridPoint : Impl Op Tst := opsImpl% [D, i, j] (Center, Radius) → (S) {
  let T ← alloc 9;
  run gridPointWithScratch.body [D, i, j] (Center, Radius, T, S)
}

private def gridWords (M : Machine ℝ) (center : ℝ × ℝ) (radius : ℝ) (D i j : ℕ) : ℝ × ℝ :=
  let a := M.sub (M.div (M.mul 2 (i : ℝ)) (D : ℝ)) 1
  let b := M.sub (M.div (M.mul 2 (j : ℝ)) (D : ℝ)) 1
  (M.add center.1 (M.mul radius a), M.add center.2 (M.mul radius b))

private def gridPrefix (M : Machine ℝ) (t : ℕ × ℕ) (radius : ℝ) (D i j : ℕ) :=
  let a₀ := M.mul 2 (i : ℝ)
  let a₁ := M.div a₀ (D : ℝ)
  let a₂ := M.sub a₁ 1
  let b₀ := M.mul 2 (j : ℝ)
  let b₁ := M.div b₀ (D : ℝ)
  let b₂ := M.sub b₁ 1
  [((t.1, t.2 + 5), a₀), ((t.1, t.2 + 5), a₁), ((t.1, t.2 + 5), a₂),
   ((t.1, t.2 + 6), b₀), ((t.1, t.2 + 6), b₁), ((t.1, t.2 + 6), b₂),
   ((t.1, t.2 + 7), M.mul radius a₂), ((t.1, t.2 + 8), M.mul radius b₂)]

private def gridTrace (M : Machine ℝ) (t s : ℕ × ℕ) (center : ℝ × ℝ)
    (radius : ℝ) (D i j : ℕ) :=
  let p := gridWords M center radius D i j
  gridPrefix M t radius D i j ++ [(s, p.1), ((s.1, s.2 + 1), p.2)]

private theorem eval_grid {M : Machine ℝ} {m : Mem ℝ} {c r t s : ℕ × ℕ}
    {center : ℝ × ℝ} {radius : ℝ} {D i j : ℕ}
    (htc : t.1 ≠ c.1) (htr : t.1 ≠ r.1) (hts : t.1 ≠ s.1)
    (hcs : (c.1, c.2 + 1) ≠ s)
    (hc0 : m.store.get c.1 c.2 = some center.1)
    (hc1 : m.store.get c.1 (c.2 + 1) = some center.2)
    (hr : m.store.get r.1 r.2 = some radius)
    (h0 : m.store.get t.1 t.2 = some (i : ℝ))
    (h1 : m.store.get t.1 (t.2 + 1) = some (j : ℝ))
    (h2 : m.store.get t.1 (t.2 + 2) = some (D : ℝ))
    (h3 : m.store.get t.1 (t.2 + 3) = some 1)
    (h4 : m.store.get t.1 (t.2 + 4) = some 2) :
    ScalarIns.evalBlock M.eval (Env.frame [D, i, j] [c, r, t, s]) gridInstructions
      m.store.cellFn = some (gridTrace M t s center radius D i j) := by
  have hct := Ne.symm htc
  have hrt := Ne.symm htr
  have hst := Ne.symm hts
  rcases c with ⟨cb, co⟩
  rcases r with ⟨rb, ro⟩
  rcases t with ⟨tb, toff⟩
  rcases s with ⟨sb, so⟩
  have hupd (g : ℕ × ℕ → Option ℝ) (u w : ℕ × ℕ) (v : Option ℝ) :
      Function.update g u v w = if w = u then v else g w := Function.update_apply ..
  have hpair := @Prod.mk.injEq ℕ ℕ
  dsimp only [gridInstructions, gridScratch, gridTrace, gridPrefix, gridWords,
    Env.frame, Store.cellFn]
  repeat' first
  | rw [ScalarIns.evalBlock.eq_def]
    simp only [Store.cellFn, Machine.eval, Operand.evalList, Operand.eval, IExp.eval,
      List.cons_append, List.nil_append, List.map_cons, List.map_nil,
      List.getElem?_cons_zero, List.getElem?_cons_succ, List.mapM_cons, List.mapM_nil,
      Option.pure_def, Option.bind_eq_bind, Option.bind_some, Option.map_some,
      Nat.add_zero, and_false, false_and, if_true, if_false,
      Nat.add_left_cancel_iff, Nat.reduceEqDiff, *]

private theorem gridWords_eq {M : Machine ℝ} (hE : ExactModel id M)
    (center : ℂ) (radius : ℝ) {D : ℕ} (hD : 1 ≤ D) (i j : ℕ) :
    gridWords M (center.re, center.im) radius D i j =
      ((gridPointValue center radius D i j).re, (gridPointValue center radius D i j).im) := by
  have hadd (a b : ℝ) : M.add a b = a + b := hE.add a b
  have hsub (a b : ℝ) : M.sub a b = a - b := hE.sub a b
  have hmul (a b : ℝ) : M.mul a b = a * b := hE.mul a b
  have hne : (D : ℝ) ≠ 0 := by exact_mod_cast (show D ≠ 0 by omega)
  have hdiv (a : ℝ) : M.div a (D : ℝ) = a / (D : ℝ) := hE.div a _ hne
  apply Prod.ext <;> simp [gridWords, hdiv, hadd, hsub, hmul, gridPointValue]

omit [Has IndexOp Op] in
private theorem gridArithmetic_writes {M : Machine ℝ} {I : Interp Op Tst ℝ}
    (hS : IsScalar M I) (hE : ExactModel id M) {τ : Tape ℝ} {m : Mem ℝ}
    {c r t s : ℕ × ℕ} {center : ℂ} {radius : ℝ} {D i j : ℕ}
    (hD : 1 ≤ D) (htc : t.1 ≠ c.1) (htr : t.1 ≠ r.1) (hts : t.1 ≠ s.1)
    (hcs : (c.1, c.2 + 1) ≠ s)
    (hc0 : m.store.get c.1 c.2 = some center.re)
    (hc1 : m.store.get c.1 (c.2 + 1) = some center.im)
    (hr : m.store.get r.1 r.2 = some radius)
    (h0 : m.store.get t.1 t.2 = some (i : ℝ))
    (h1 : m.store.get t.1 (t.2 + 1) = some (j : ℝ))
    (h2 : m.store.get t.1 (t.2 + 2) = some (D : ℝ))
    (h3 : m.store.get t.1 (t.2 + 3) = some 1)
    (h4 : m.store.get t.1 (t.2 + 4) = some 2)
    (ht : t.2 + 9 ≤ m.store.len t.1) (hs : s.2 + 2 ≤ m.store.len s.1) :
    Writes .total I τ (.scalarBlock (gridInstructions.map ScalarIns.lift))
      (Env.frame [D, i, j] [c, r, t, s])
      (Store.inBlock t.1 t.2 9 ⊔ Store.inBlock s.1 s.2 2)
      (fun μ => μ.pos = m.pos ∧ μ.store.readBlock s.1 s.2 2 =
        some [(gridPointValue center radius D i j).re,
          (gridPointValue center radius D i j).im]) m := by
  have hev := eval_grid (M := M) (m := m) (center := (center.re, center.im))
    htc htr hts hcs hc0 hc1 hr h0 h1 h2 h3 h4
  have hroom : ∀ w ∈ gridTrace M t s (center.re, center.im) radius D i j,
      w.1.2 < m.store.len w.1.1 := by
    intro w hw
    simp only [gridTrace, gridPrefix, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false, or_assoc] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp <;> omega
  refine (writes_machineScalarBlock (τ := τ) hS hev hroom).mono ?_ ?_
  · intro b k hk
    simp only [gridTrace, gridPrefix, List.map_append, List.map_cons, List.map_nil,
      Fp.cells, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq,
      or_assoc] at hk
    rcases hk with h | h | h | h | h | h | h | h | h | h <;>
      obtain ⟨rfl, rfl⟩ := h <;> fp_mem
  · rintro μ _ rfl
    have he := gridWords_eq hE center radius hD i j
    have hout := Pair.readBlock_updCells_pair (m := m)
      (prior := gridPrefix M t radius D i j)
      (v := gridWords M (center.re, center.im) radius D i j) hs
    exact ⟨rfl, by simpa only [gridTrace, he] using hout⟩

/-- Five actual dimension literals and ten scalar operations compute the requested grid
point. The denominator is positive; both coordinate numerators and the radius are arbitrary.
The output is disjoint from the center, and the scratch buffer is fresh. -/
theorem gridPointWithScratch_writes {M : Machine ℝ} {I : Interp Op Tst ℝ}
    (hS : IsScalar M I) (hE : ExactModel id M) (hL : IsIndexLit M I)
    {τ : Tape ℝ} {m : Mem ℝ} {c r t s : ℕ × ℕ} {center : ℂ} {radius : ℝ}
    {D i j : ℕ} (hD : 1 ≤ D)
    (htc : t.1 ≠ c.1) (htr : t.1 ≠ r.1) (hts : t.1 ≠ s.1)
    (hcs : Fp.Disj (Store.inBlock c.1 c.2 2) (Store.inBlock s.1 s.2 2))
    (hc0 : m.store.get c.1 c.2 = some center.re)
    (hc1 : m.store.get c.1 (c.2 + 1) = some center.im)
    (hr : m.store.get r.1 r.2 = some radius)
    (ht : t.2 + 9 ≤ m.store.len t.1) (hs : s.2 + 2 ≤ m.store.len s.1) :
    Writes .total I τ gridPointWithScratch.body (Env.frame [D, i, j] [c, r, t, s])
      (Store.inBlock t.1 t.2 9 ⊔ Store.inBlock s.1 s.2 2)
      (fun μ => μ.pos = m.pos ∧ μ.store.readBlock s.1 s.2 2 =
        some [(gridPointValue center radius D i j).re,
          (gridPointValue center radius D i j).im]) m := by
  let zs := [(t.1, t.2), (t.1, t.2 + 1), (t.1, t.2 + 2),
    (t.1, t.2 + 3), (t.1, t.2 + 4)]
  have hp := writes_indexBlock (m := m) (τ := τ) (ρ := Env.frame [D, i, j] [c, r, t, s]) hL
    gridLiterals (ns := [i, j, D, 1, 2]) (zs := zs) rfl rfl
    (by simp only [zs, gridLiterals, List.length_cons, List.length_nil,
          List.replicate_succ, Fp.Apart, Fp.blocks, Fp.disj_sup_right, Fp.disj_bot_right]
        repeat' apply And.intro
        all_goals try exact True.intro
        all_goals intro b k hk hl; dsimp only [Store.inBlock] at hk hl; omega)
    (by simp only [zs, gridLiterals, List.length_cons, List.length_nil,
          List.replicate_succ, Mem.room_cons];
        exact ⟨by omega, by omega, by omega,
          by omega, by omega, trivial⟩)
  have hp' := hp.mono (G := Store.inBlock t.1 t.2 9) (by dsimp [zs]; fp_sub)
    (fun _ _ h => h)
  refine hp'.seq_le le_sup_left ?_
  intro μ hfr ⟨hpos, hreads⟩
  have hnat (k : ℕ) : M.lit (k : ℚ) = (k : ℝ) := by simpa using hE.lit (k : ℚ)
  have hone : M.lit 1 = 1 := by simpa using hE.lit 1
  have htwo : M.lit 2 = 2 := by simpa using hE.lit 2
  have h0 := Mem.get_of_readBlocks_getD hreads (i := 0) (v := M.lit (i : ℚ))
    (by simp [zs, gridLiterals]) rfl rfl
  have h1 := Mem.get_of_readBlocks_getD hreads (i := 1) (v := M.lit (j : ℚ))
    (by simp [zs, gridLiterals]) rfl rfl
  have h2 := Mem.get_of_readBlocks_getD hreads (i := 2) (v := M.lit (D : ℚ))
    (by simp [zs, gridLiterals]) rfl rfl
  have h3 := Mem.get_of_readBlocks_getD hreads (i := 3) (v := M.lit 1)
    (by simp [zs, gridLiterals]) rfl rfl
  have h4 := Mem.get_of_readBlocks_getD hreads (i := 4) (v := M.lit 2)
    (by simp [zs, gridLiterals]) rfl rfl
  have hc0' := (hfr.get_eq (b := c.1) (i := c.2)
    (by rintro ⟨he, _, _⟩; exact htc he.symm)).trans hc0
  have hc1' := (hfr.get_eq (b := c.1) (i := c.2 + 1)
    (by rintro ⟨he, _, _⟩; exact htc he.symm)).trans hc1
  have hr' := (hfr.get_eq (b := r.1) (i := r.2) (by rintro ⟨he, _, _⟩; exact htr he.symm)).trans hr
  have hcs' : (c.1, c.2 + 1) ≠ s := by
    simpa only [Nat.add_zero, Prod.eta] using hcs.ne_offsets (i := 1) (j := 0) (by omega) (by omega)
  refine (gridArithmetic_writes (τ := τ) hS hE hD htc htr hts hcs' hc0' hc1' hr'
    (by simpa [zs, hnat] using h0) (by simpa [zs, hnat] using h1)
    (by simpa [zs, hnat] using h2) (by simpa [zs, hone] using h3)
    (by simpa [zs, htwo] using h4) (by rw [hfr.len_eq]; exact ht)
    (by rw [hfr.len_eq]; exact hs)).mono le_rfl ?_
  intro μ' _ ⟨hp₂, hout⟩
  exact ⟨hp₂.trans hpos, hout⟩


/-- The scoped grid-point program computes the same exact point and releases all nine
scratch words. Its only surviving writes are the two output components. -/
theorem gridPoint_writes {M : Machine ℝ} {I : Interp Op Tst ℝ}
    (hS : IsScalar M I) (hE : ExactModel id M) (hL : IsIndexLit M I)
    {τ : Tape ℝ} {m : Mem ℝ} {c r s : ℕ × ℕ} {center : ℂ} {radius : ℝ}
    {D i j : ℕ} (hD : 1 ≤ D)
    (hcs : Fp.Disj (Store.inBlock c.1 c.2 2) (Store.inBlock s.1 s.2 2))
    (hc0 : m.store.get c.1 c.2 = some center.re)
    (hc1 : m.store.get c.1 (c.2 + 1) = some center.im)
    (hr : m.store.get r.1 r.2 = some radius)
    (hs : s.2 + 2 ≤ m.store.len s.1) :
    Writes .total I τ gridPoint.body (Env.frame [D, i, j] [c, r, s])
      (Store.inBlock s.1 s.2 2)
      (fun μ => μ.pos = m.pos ∧ μ.store.readBlock s.1 s.2 2 =
        some [(gridPointValue center radius D i j).re,
          (gridPointValue center radius D i j).im]) m := by
  have hcl := Store.lt_length_of_get hc0
  have hrl := Store.lt_length_of_get hr
  have hsl : s.1 < m.store.length := Store.lt_length_of_lt_len (by omega : s.2 < _)
  apply writes_allocs_readBlock (lens := [.const 9]) (ns := [9]) rfl hsl
  intro store hlen hlens hBelow
  let t : ℕ × ℕ := (m.store.length, 0)
  have ht : t.2 + 9 ≤ store.len t.1 := by
    simpa [t] using (hlens 0 (by simp)).ge
  have hbody := gridPointWithScratch_writes (i := i) (j := j) (τ := τ) (m := ⟨store, m.pos⟩)
    hS hE hL hD (by dsimp [t]; omega) (by dsimp [t]; omega)
    (by dsimp [t]; omega) hcs (hBelow.get_of hcl hc0) (hBelow.get_of hcl hc1)
    (hBelow.get_of hrl hr) ht (by rw [(hBelow s.1 hsl).1]; exact hs)
  exact (hbody.in_frame rfl rfl (by simp [Mem.Live, t, hlen]; omega)).mono
    (sup_le (Fp.inBlock_le_sup_above (by dsimp [t]; omega)) le_sup_left)
    (fun _ _ hp => hp)


end NLAlib.ShiftedQR
