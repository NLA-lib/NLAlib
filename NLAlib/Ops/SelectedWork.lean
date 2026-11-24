/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.MonomialWork
public import NLAlib.Ops.PolynomialWork

/-!
# Work of a run as an instruction count plus the weight of selected calls

A resource model often charges one unit for every instruction except a few expensive
primitives, whose weights are caller parameters of arbitrary growth. This file bounds the
weighted count of a counted run by two separate terms: the number of instructions of the static
count (the per-slot monomial of `NLAlib.Ops.stmtWorkMono`), and the number of selected calls
times an envelope of their weights. The number of selected calls is the polynomial of the tree
with every unselected subtree removed (`NLAlib.Ops.Stmt.keepCalls`), so it is not inflated by the
cheap instructions.

## Main definitions

* `NLAlib.Ops.Stmt.hasCall`: whether a tree contains a selected call.
* `NLAlib.Ops.Stmt.keepCalls`: the tree with every subtree without a selected call removed.

## Main results

* `NLAlib.Ops.Count.lift_le_size_add`: a weight at most one plus `g` is at most the number of
  instructions plus the weight `g`.
* `NLAlib.Ops.stmtWeightedCost_keepCalls`: removing unselected subtrees keeps the weighted cost of
  weights supported on the selected calls.
* `NLAlib.Ops.Program.exec_lift_le_add_selected`: the weighted count of a run is at most the
  monomial bound of its instructions plus the selected-call polynomial times the envelope.
-/

@[expose] public section

namespace NLAlib.Ops

variable {Op Tst : Type}

namespace Count

/-- `NLAlib.Ops.Count.lift` is monotone in the weight. -/
theorem lift_le_lift {f g : Op ⊕ Tst → List ℕ → ℕ} (h : ∀ k d, f k d ≤ g k d)
    (c : Count Op Tst) : lift f c ≤ lift g c := by
  induction c using Finsupp.induction with
  | zero => simp
  | single_add k n c _ _ ih =>
    rw [map_add, map_add, lift_single, lift_single, smul_eq_mul, smul_eq_mul]
    exact Nat.add_le_add (Nat.mul_le_mul_left _ (h _ _)) ih

/-- `NLAlib.Ops.Count.lift` is additive in the weight. -/
theorem lift_add_weight (f g : Op ⊕ Tst → List ℕ → ℕ) (c : Count Op Tst) :
    lift (fun k d => f k d + g k d) c = lift f c + lift g c := by
  induction c using Finsupp.induction with
  | zero => simp
  | single_add k n c _ _ ih =>
    simp only [map_add, lift_single, smul_eq_mul, ih]
    ring

/-- A weight at most one plus `g` gives at most the number of instructions plus the weight
`g`. -/
theorem lift_le_size_add {f g : Op ⊕ Tst → List ℕ → ℕ} (h : ∀ k d, f k d ≤ 1 + g k d)
    (c : Count Op Tst) : lift f c ≤ Count.size c + lift g c := by
  rw [Count.size, ← lift_add_weight]
  exact lift_le_lift h c

end Count

/-- Whether the tree contains a call of an operation selected by `sel`. -/
def Stmt.hasCall (sel : Op → Bool) : Stmt Op Tst → Bool
  | .skip | .abort => false
  | .seq s t | .ite _ _ _ s t | .whileFuel _ _ _ _ s t => s.hasCall sel || t.hasCall sel
  | .call o _ _ _ => sel o
  | .bindIdx _ _ _ s | .allocAs _ _ s | .loop _ s | .frame _ _ s | .note _ s => s.hasCall sel

/-- **The selected calls of a tree**: every unselected call, and every branch, capped loop, index
binding or loop that contains no selected call, is replaced by `skip`. The tree is used only for
counting; it is not run. -/
def Stmt.keepCalls (sel : Op → Bool) : Stmt Op Tst → Stmt Op Tst
  | .skip => .skip
  | .abort => .abort
  | .seq s t => .seq (s.keepCalls sel) (t.keepCalls sel)
  | .call o ds a b => if sel o then .call o ds a b else .skip
  | .ite q ds a s t =>
      if s.hasCall sel || t.hasCall sel then .ite q ds a (s.keepCalls sel) (t.keepCalls sel)
      else .skip
  | .whileFuel f q ds a s t =>
      if s.hasCall sel || t.hasCall sel then
        .whileFuel f q ds a (s.keepCalls sel) (t.keepCalls sel)
      else .skip
  | .bindIdx q a b s => if s.hasCall sel then .bindIdx q a b (s.keepCalls sel) else .skip
  | .allocAs f l s => .allocAs f l (s.keepCalls sel)
  | .loop n s => if s.hasCall sel then .loop n (s.keepCalls sel) else .skip
  | .frame ds a s => .frame ds a (s.keepCalls sel)
  | .note n s => .note n (s.keepCalls sel)

section Selected

variable {sel : Op → Bool} {g : Op → List ℕ → ℕ}

/-- A tree without a selected call has weighted cost zero under a weight supported on the
selected calls, with zero query weight. -/
theorem stmtWeightedCost_eq_zero_of_hasCall (hg : ∀ o ds, sel o = false → g o ds = 0) :
    ∀ (s : Stmt Op Tst), s.hasCall sel = false → ∀ idx,
      stmtWeightedCost g (fun _ _ => 0) s idx = 0
  | .skip, _, _ | .abort, _, _ => rfl
  | .seq s t, h, idx => by
    simp only [Stmt.hasCall, Bool.or_eq_false_iff] at h
    simp [stmtWeightedCost, stmtWeightedCost_eq_zero_of_hasCall hg s h.1,
      stmtWeightedCost_eq_zero_of_hasCall hg t h.2]
  | .call o ds _ _, h, idx => by
    simp only [stmtWeightedCost]
    cases IExp.evalList idx ds <;> simp [hg o _ h]
  | .ite q ds _ s t, h, idx => by
    simp only [Stmt.hasCall, Bool.or_eq_false_iff] at h
    simp only [stmtWeightedCost]
    cases IExp.evalList idx ds <;> simp [stmtWeightedCost_eq_zero_of_hasCall hg s h.1,
      stmtWeightedCost_eq_zero_of_hasCall hg t h.2]
  | .whileFuel fuel q ds _ s t, h, idx => by
    simp only [Stmt.hasCall, Bool.or_eq_false_iff] at h
    have h0 (x : Option (List ℕ)) : (x.map fun _ => (0 : ℕ)).getD 0 = 0 := by cases x <;> rfl
    simp [stmtWeightedCost, h0, stmtWeightedCost_eq_zero_of_hasCall hg s h.1,
      stmtWeightedCost_eq_zero_of_hasCall hg t h.2]
  | .bindIdx q _ bound s, h, idx => by
    simp [stmtWeightedCost, stmtWeightedCost_eq_zero_of_hasCall hg s h]
  | .allocAs _ _ s, h, idx => stmtWeightedCost_eq_zero_of_hasCall hg s h idx
  | .loop n s, h, idx => by
    simp [stmtWeightedCost, stmtWeightedCost_eq_zero_of_hasCall hg s h]
  | .frame ds args s, h, idx => by
    simp only [stmtWeightedCost]
    split
    · exact stmtWeightedCost_eq_zero_of_hasCall hg s h _
    · rfl
  | .note _ s, h, idx => stmtWeightedCost_eq_zero_of_hasCall hg s h idx

/-- Removing unselected subtrees keeps the weighted cost of a weight supported on the
selected calls, with zero query weight. -/
theorem stmtWeightedCost_keepCalls (hg : ∀ o ds, sel o = false → g o ds = 0) :
    ∀ (s : Stmt Op Tst) idx, stmtWeightedCost g (fun _ _ => 0) (s.keepCalls sel) idx =
      stmtWeightedCost g (fun _ _ => 0) s idx
  | .skip, _ | .abort, _ => rfl
  | .seq s t, idx => by
    simp [Stmt.keepCalls, stmtWeightedCost, stmtWeightedCost_keepCalls hg s,
      stmtWeightedCost_keepCalls hg t]
  | .call o ds _ _, idx => by
    simp only [Stmt.keepCalls]
    split
    · rfl
    · rename_i ho
      simp only [Bool.not_eq_true] at ho
      simp only [stmtWeightedCost]
      cases IExp.evalList idx ds <;> simp [hg o _ ho]
  | .ite q ds _ s t, idx => by
    simp only [Stmt.keepCalls]
    split
    · simp [stmtWeightedCost, stmtWeightedCost_keepCalls hg s, stmtWeightedCost_keepCalls hg t]
    · rename_i h
      simp only [Bool.not_eq_true] at h
      exact (stmtWeightedCost_eq_zero_of_hasCall hg (.ite q ds _ s t) h idx).symm
  | .whileFuel fuel q ds _ s t, idx => by
    simp only [Stmt.keepCalls]
    split
    · simp [stmtWeightedCost, stmtWeightedCost_keepCalls hg s, stmtWeightedCost_keepCalls hg t]
    · rename_i h
      simp only [Bool.not_eq_true] at h
      exact (stmtWeightedCost_eq_zero_of_hasCall hg (.whileFuel fuel q ds _ s t) h idx).symm
  | .bindIdx q a bound s, idx => by
    simp only [Stmt.keepCalls]
    split
    · simp [stmtWeightedCost, stmtWeightedCost_keepCalls hg s]
    · rename_i h
      simp only [Bool.not_eq_true] at h
      exact (stmtWeightedCost_eq_zero_of_hasCall hg (.bindIdx q a bound s) h idx).symm
  | .allocAs _ _ s, idx => stmtWeightedCost_keepCalls hg s idx
  | .loop n s, idx => by
    simp only [Stmt.keepCalls]
    split
    · simp [stmtWeightedCost, stmtWeightedCost_keepCalls hg s]
    · rename_i h
      simp only [Bool.not_eq_true] at h
      exact (stmtWeightedCost_eq_zero_of_hasCall hg (.loop n s) h idx).symm
  | .frame ds args s, idx => by
    simp only [Stmt.keepCalls, stmtWeightedCost]
    split
    · exact stmtWeightedCost_keepCalls hg s _
    · rfl
  | .note _ s, idx => stmtWeightedCost_keepCalls hg s idx

end Selected

/-- The weighted count of a run: instructions plus selected calls. Let the weight `f` of
every operation, structural instruction and query be at most one plus `g`, where `g` charges only
operations selected by `sel` (and no query). Then every successful counted run of the program
`p` has weighted count at most the monomial bound of the instructions of its static count, at
bases `bs`, each at least $1$, bounding its initial index slots, plus the polynomial of its
selected calls (`NLAlib.Ops.Stmt.keepCalls`) at a base at least $2$, times a ceiling `E` of `g`
on the dimensions the selected calls may have. -/
theorem Program.exec_lift_le_add_selected {K : Type} {r buffers : ℕ}
    (p : Program Op Tst r buffers) (R : ResourceModel Op Tst)
    {I : Interp Op Tst K} {τ : Tape K} {formats : Fin buffers → StorageFormat}
    {d : Fin r → ℕ} {m : Mem K} {st : St (Op ⊕ Bookkeeping) Tst K}
    (hr : exec p I R formats τ d m = some st) (sel : Op ⊕ Bookkeeping → Bool)
    {f : (Op ⊕ Bookkeeping) ⊕ Tst → List ℕ → ℕ} {g : Op ⊕ Bookkeeping → List ℕ → ℕ}
    (hfg : ∀ k ds, f k ds ≤ 1 + Sum.elim g (fun _ _ => 0) k ds)
    (hg : ∀ o ds, sel o = false → g o ds = 0)
    {bs : List ℕ} (hb : ∀ b ∈ bs, 1 ≤ b) {σ : List WorkMono}
    (hσ : SlotsLe bs (Program.environment (b := buffers) d).idx σ)
    {base E : ℕ} {degrees : List ℕ} (hbase : 2 ≤ base)
    (hi : List.Forall₂ (fun v e => v ≤ base ^ e)
      (Program.environment (b := buffers) d).idx degrees)
    (hE : WorkEnvelope g (fun (_ : Tst) _ => 0) (p.body.instrument.keepCalls sel).callArity
      (base ^ (p.body.instrument.keepCalls sel).callDegreeAt degrees) E) :
    Count.lift f st.cost ≤ (stmtWorkMono p.body.instrument σ).eval bs +
      (p.body.instrument.keepCalls sel).workCoefficient *
        base ^ (p.body.instrument.keepCalls sel).workDegreeAt degrees * E := by
  refine (Count.lift_le_size_add hfg st.cost).trans (Nat.add_le_add ?_ ?_)
  · exact (size_mono (exec_static hr).1).trans
      (size_stmtCost_le_stmtWorkMono hb p.body.instrument hσ)
  · unfold exec at hr
    split_ifs at hr with ht
    obtain ⟨raw, hraw, rfl⟩ := Option.map_eq_some_iff.mp hr
    have hcost := evalCounted_weight_le g (fun _ _ => 0) hraw
    simp only [St.init, map_zero, Nat.zero_add] at hcost
    rw [← stmtWeightedCost_keepCalls hg] at hcost
    exact hcost.trans (stmtWeightedCost_le_coefficient_mul_pow g _ _ hbase hi hE)

end NLAlib.Ops
