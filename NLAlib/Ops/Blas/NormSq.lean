/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Logic.Builder
public import NLAlib.Ops.Logic.Tactic
public import NLAlib.Ops.Logic.RoutineIntro
public import NLAlib.Ops.RoutineSyntax

/-!
# Squared modulus of an interleaved scalar pair

The squared components and their sum are computed by two real multiplications and one
addition. The exact word theorem is local to these three calls and uses a separate three-word
view for their outputs.

## Main results

* `NLAlib.Ops.PairScalar.normSqRoutine`: the routine `[] (X : 2) → (T : 3)`, on the tree
  `NLAlib.Ops.PairScalar.normSq`.
* `NLAlib.Ops.PairScalar.normSqRoutine_meets`: its judgment, on any scalar machine.
* `NLAlib.Ops.PairScalar.normSq_writes_word`, `NLAlib.Ops.PairScalar.normSq_writes`: the
  judgment read at cells.
-/

@[expose] public section

namespace NLAlib.Ops.PairScalar

variable {Op Tst : Type} [Has ScalarOp Op]

/-- Compute the squared components in output cells zero and one, and their sum in cell two. -/
def normSq : Stmt Op Tst := ops% [] (X) → (T) {
  call (Has.inj ScalarOp.mul) [] (X, X) → (T);
  call (Has.inj ScalarOp.mul) [] (X[1], X[1]) → (T[1]);
  call (Has.inj ScalarOp.add) [] (T, T[1]) → (T[2])
}

/-- The squared modulus of a pair as a routine: `[] (X : 2) → (T : 3)`, the two blocks apart;
they may be in one buffer. -/
def normSqRoutine : Routine Op Tst :=
  routine% [] (X : 2) → (T : 3) by blocks := normSq

/-- The three written words are the two machine squares and their machine sum
`fl(fl(xr·xr) + fl(xi·xi))`. -/
def normSqSpec (M : Machine ℝ) : Routine.Spec ℝ :=
  spec% [] ([xr, xi]) → (ts) ensures
    ts = [M.mul xr xr, M.mul xi xi, M.add (M.mul xr xr) (M.mul xi xi)]

/-- The squared modulus meets its specification on any scalar machine: two squares and one
addition, with no accuracy hypothesis. -/
theorem normSqRoutine_meets {M : Machine ℝ} {I : Interp Op Tst ℝ} (hS : IsScalar M I) :
    (normSqRoutine (Op := Op) (Tst := Tst)).Meets I (normSqSpec M) := by
  routine_intro [] (x, t) reads (xs)
  obtain ⟨xr, xi, rfl⟩ : ∃ xr xi, xs = [xr, xi] := by
    have h := Store.length_of_readBlock hxs
    match xs, h with
    | [a, b], _ => exact ⟨a, b, rfl⟩
  have hxr : m.store.get x.1 x.2 = some xr := by
    simpa using Store.get_of_readBlock hxs (j := 0) (by omega) 0
  have hxi : m.store.get x.1 (x.2 + 1) = some xi := by
    simpa using Store.get_of_readBlock hxs (j := 1) (by omega) 0
  have hsep' : Fp.Disj (Store.inBlock x.1 x.2 2) (Store.inBlock t.1 t.2 3) := by
    have h : Fp.Disj (Fp.blocks [t] [3]) (Fp.blocks [x] [2]) := hblocks.2.1
    simpa [Fp.blocks] using h.symm
  have hxLive := Store.lt_length_of_get hxr
  have htLive := Store.lt_length_of_lt_len (show t.2 < m.store.len t.1 by omega)
  unfold normSq
  refine (writes_call_bin (hS .mul) rfl rfl trivial hxr hxr rfl
    (fun _ => ⟨by room, by room⟩)).seq_le (by fp_sub) ?_
  intro m₁ hfr₁ ⟨hp₁, hRe⟩
  have hxi₁ := hfr₁.keep (Store.readsOnly_get _ _ _)
    (hsep'.symm.mono (by fp_sub) (by fp_sub)) hxi
  refine (writes_call_bin (hS .mul) rfl rfl trivial hxi₁ hxi₁ rfl
    (fun _ => ⟨by room, by room⟩)).seq_le (by fp_sub) ?_
  intro m₂ hfr₂ ⟨hp₂, hIm⟩
  have hRe₂ := hfr₂.keep (Store.readsOnly_get _ _ _) (by disjoint) hRe
  refine (writes_call_bin (hS .add) rfl rfl trivial hRe₂ hIm rfl
    (fun _ => ⟨by room, by room⟩)).mono (by fp_sub) ?_
  intro m₃ hfr₃ ⟨hp₃, hSum⟩
  have hRe₃ := hfr₃.keep (Store.readsOnly_get _ _ _) (by disjoint) hRe₂
  have hIm₃ := hfr₃.keep (Store.readsOnly_get _ _ _) (by disjoint) hIm
  refine ⟨hp₃.trans (hp₂.trans hp₁), [_], Mem.readBlocks_of_cons
    (Store.readBlock_succ_of (Store.readBlock_succ_of (Store.readBlock_one_of_get hRe₃) hIm₃)
      hSum) rfl, rfl⟩

/-- The judgment of `NLAlib.Ops.PairScalar.normSqRoutine` read at cells: output cell two holds
the machine word `fl(fl(xr·xr) + fl(xi·xi))`. A corollary of
`NLAlib.Ops.PairScalar.normSqRoutine_meets`, kept because its callers hold the two input words
as cells of a matrix entry inside a loop rule, and read only the third output cell. -/
theorem normSq_writes_word {M : Machine ℝ} {I : Interp Op Tst ℝ}
    (hS : IsScalar M I) {τ : Tape ℝ} {m : Mem ℝ}
    {x t : ℕ × ℕ} {xr xi : ℝ}
    (hxr : m.store.get x.1 x.2 = some xr)
    (hxi : m.store.get x.1 (x.2 + 1) = some xi)
    (hroom : t.2 + 3 ≤ m.store.len t.1)
    (hsep : Fp.Disj (Store.inBlock x.1 x.2 2) (Store.inBlock t.1 t.2 3)) :
    Writes .total I τ (normSq (Op := Op) (Tst := Tst)) (Env.frame [] [x, t])
      (Store.inBlock t.1 t.2 3)
      (fun m' => m'.pos = m.pos ∧
        m'.store.get t.1 (t.2 + 2) = some (M.add (M.mul xr xr) (M.mul xi xi))) m := by
  have hl : m.Live [x, t] := by
    simp only [Mem.live_cons, Mem.live_nil, and_true]
    exact ⟨Store.lt_length_of_get hxr,
      Store.lt_length_of_lt_len (show t.2 < m.store.len t.1 by omega)⟩
  have hx : m.store.readBlock x.1 x.2 2 = some [xr, xi] :=
    Store.readBlock_succ_of (Store.readBlock_one_of_get hxr) hxi
  have hrooms : m.Room [t] [3] := by
    simpa only [Mem.room_cons, Mem.room_nil, and_true] using hroom
  have h := normSqRoutine_meets (Op := Op) (Tst := Tst) hS [] [x, t] τ m [[xr, xi]] rfl rfl
    hl (by routine_sep) (Mem.readBlocks_of_cons hx rfl) trivial hrooms
  refine h.mono (by fp_sub) fun m' _ ⟨hpos, ys, hys, hpost⟩ => ?_
  routine_nf at hys hpos
  split_reads hys as (zs)
  obtain rfl : zs = _ := hpost
  exact ⟨hpos, by simpa using Store.get_of_readBlock hzs (j := 2) (by omega) 0⟩

/-- The same reading under an exact machine: output cell two holds $x_r^2 + x_i^2$. A corollary
of `NLAlib.Ops.PairScalar.normSqRoutine_meets`, kept for the same callers as
`NLAlib.Ops.PairScalar.normSq_writes_word`. -/
theorem normSq_writes {M : Machine ℝ} {I : Interp Op Tst ℝ}
    (hS : IsScalar M I) (hE : ExactModel id M) {τ : Tape ℝ} {m : Mem ℝ}
    {x t : ℕ × ℕ} {xr xi : ℝ}
    (hxr : m.store.get x.1 x.2 = some xr)
    (hxi : m.store.get x.1 (x.2 + 1) = some xi)
    (hroom : t.2 + 3 ≤ m.store.len t.1)
    (hsep : Fp.Disj (Store.inBlock x.1 x.2 2) (Store.inBlock t.1 t.2 3)) :
    Writes .total I τ (normSq (Op := Op) (Tst := Tst)) (Env.frame [] [x, t])
      (Store.inBlock t.1 t.2 3)
      (fun m' => m'.pos = m.pos ∧
        m'.store.get t.1 (t.2 + 2) = some (xr ^ 2 + xi ^ 2)) m := by
  have hmul (u v : ℝ) : M.mul u v = u * v := hE.mul u v
  have hadd (u v : ℝ) : M.add u v = u + v := hE.add u v
  simpa only [hmul, hadd, pow_two] using normSq_writes_word (τ := τ) hS hxr hxi hroom hsep

/-- Under the standard model with $0 \le u \le 1$, the rounded sum of rounded squares
$\mathrm{fl}(\mathrm{fl}(x^2) + \mathrm{fl}(y^2))$ lies between $(1-u)^2(x^2+y^2)$ and
$(1+u)^2(x^2+y^2)$. -/
theorem _root_.NLAlib.Ops.StdModel.add_mul_self_bounds {M : Machine ℝ} {u : ℝ}
    (hM : StdModel u id M) (hu : 0 ≤ u) (hu1 : u ≤ 1) (x y : ℝ) :
    (1 - u) ^ 2 * (x ^ 2 + y ^ 2) ≤ M.add (M.mul x x) (M.mul y y) ∧
      M.add (M.mul x x) (M.mul y y) ≤ (1 + u) ^ 2 * (x ^ 2 + y ^ 2) := by
  have hp := abs_le.mp (hM.mul x x)
  have hq := abs_le.mp (hM.mul y y)
  have hs := abs_le.mp (hM.add (M.mul x x) (M.mul y y))
  simp only [id_eq] at hp hq hs
  have hx : 0 ≤ x * x := mul_self_nonneg x
  have hy : 0 ≤ y * y := mul_self_nonneg y
  rw [abs_of_nonneg hx] at hp
  rw [abs_of_nonneg hy] at hq
  have hS : (1 - u) * (x * x + y * y) ≤ M.mul x x + M.mul y y := by nlinarith
  have hS' : M.mul x x + M.mul y y ≤ (1 + u) * (x * x + y * y) := by nlinarith
  have hS0 : 0 ≤ M.mul x x + M.mul y y := by nlinarith
  rw [abs_of_nonneg hS0] at hs
  constructor <;> nlinarith

end NLAlib.Ops.PairScalar
