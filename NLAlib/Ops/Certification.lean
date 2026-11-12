/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Cert
public import NLAlib.Ops.Transfer

/-!
# Shared adapters for canonical algorithm certification

Supplied buffers remain explicit data. Their initial memory facts follow from their finite
indices, and total conditional program proofs supply total word-level preconditions. Original
operation counts can be projected out of the complete mandatory instrumented count without
losing the separate accounting guarantee on structural instructions.

## Main results

* `NLAlib.Ops.Problem.initial_readBlock`: a supplied initialized buffer can be read directly.
* `NLAlib.Ops.ConditionalRuns.wp`: total conditional execution supplies total program logic.
* `NLAlib.Ops.original_stmtCost_instrument`: structural instrumentation preserves raw counts.
-/

@[expose] public section

namespace NLAlib.Ops

variable {Op Tst K : Type} {r b : ℕ} {P : Problem K r b}

/-- The initial stack has exactly the declared number of supplied buffers. -/
@[simp] theorem Problem.length_initial (d : Fin r → ℕ) (x : P.Input d) :
    (P.initial d x).store.length = b := by
  simp [Problem.initial]

/-- A supplied buffer retains its actual capacity in the initial memory. -/
@[simp] theorem Problem.initial_len (d : Fin r → ℕ) (x : P.Input d) (i : Fin b) :
    (P.initial d x).store.len i.val = (x.val.2 i).length := by
  simp [Problem.initial, Store.len]

/-- Initial reads address the supplied words, with no algorithm-dependent initializer. -/
@[simp] theorem Problem.initial_get (d : Fin r → ℕ) (x : P.Input d) (i : Fin b) (j : ℕ) :
    (P.initial d x).store.get i.val j = ((x.val.2 i)[j]?).join := by
  simp [Problem.initial, Store.get]

/-- A buffer supplied as initialized words reads back that very word list. -/
theorem Problem.initial_readBlock (d : Fin r → ℕ) (x : P.Input d) (i : Fin b)
    {xs : List K} (h : x.val.2 i = xs.map some) :
    (P.initial d x).store.readBlock i.val 0 xs.length = some xs := by
  refine Store.readBlock_eq_some_iff.mpr ⟨rfl, fun j hj => ?_⟩
  simp only [Nat.zero_add, Problem.initial_get, h, List.getElem?_map]
  cases xs[j]? <;> rfl

/-- Declared buffer capacities determine resident payload, including uninitialized slots. -/
theorem Problem.initialBytes_of_lengths (d : Fin r → ℕ) (x : P.Input d)
    (lens : Fin b → ℕ) (h : ∀ i, (x.val.2 i).length = lens i) :
    P.initialBytes d x = (List.ofFn fun i => (P.formats i).bytes * lens i).sum := by
  simp only [Problem.initialBytes, h]

/-- A successful conditional run provides total word-level logic. Raw count/workspace bounds
are not promoted here; canonical certification separately requires all instrumented bounds. -/
theorem ConditionalRuns.wp {I : Interp Op Tst K} {W : Op → List ℕ → ℕ} {τ : Tape K}
    {s : Stmt Op Tst} {ρ : Env} {m : Mem K} {c : Count Op Tst} {p : ℕ} {Q : Mem K → Prop}
    (h : ConditionalRuns I W τ s ρ m c p Q) : Wp .total I τ s ρ Q m := by
  obtain ⟨st, hr, _, _, hQ⟩ := h
  exact ⟨st.mem, run_of_exec hr, hQ⟩

/-- Original-operation projection preserves pointwise worst-case branch counts. -/
theorem Count.original_sup (c d : Count (Op ⊕ Bookkeeping) Tst) :
    Count.original (c ⊔ d) = Count.original c ⊔ Count.original d := by
  ext k
  simp only [Count.original_apply, Finsupp.sup_apply]

/-- Original-operation projection preserves finite worst-case loop bounds. -/
theorem Count.original_finset_sup {α : Type} (s : Finset α)
    (f : α → Count (Op ⊕ Bookkeeping) Tst) :
    Count.original (s.sup f) = s.sup (fun i => Count.original (f i)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    change Count.original (0 : Count (Op ⊕ Bookkeeping) Tst) = 0
    exact map_zero _
  | @insert a s ha ih => simp only [Finset.sup_insert, Count.original_sup, ih]

/-- Original calls retain their dimension-dependent static count. -/
theorem original_useCost (o : Op) (ds : List IExp) (idx : List ℕ) :
    Count.original (useCost (.inl o) ds idx : Count (Op ⊕ Bookkeeping) Tst) =
      useCost o ds idx := by
  unfold useCost
  cases IExp.evalList idx ds <;> simp

/-- A structural instruction has no original-operation count, even when dimensions fail. -/
theorem original_useCost_inr (o : Bookkeeping) (ds : List IExp) (idx : List ℕ) :
    Count.original (useCost (.inr o) ds idx : Count (Op ⊕ Bookkeeping) Tst) = 0 := by
  unfold useCost
  cases IExp.evalList idx ds <;> simp

/-- Query counts are preserved independently of structural instrumentation. -/
theorem original_testCost (q : Tst) (ds : List IExp) (idx : List ℕ) :
    Count.original (testCost q ds idx : Count (Op ⊕ Bookkeeping) Tst) =
      testCost q ds idx := by
  unfold testCost
  cases IExp.evalList idx ds <;> simp

/-- Bookkeeping-only syntax has no original calls or queries. -/
theorem original_stmtCost_tally (ks : List Bookkeeping) (idx : List ℕ) :
    Count.original (stmtCost (tally (Op := Op) (Tst := Tst) ks) idx) = 0 := by
  induction ks with
  | nil => simp [tally, stmtCost]
  | cons k ks ih => simp [tally, stmtCost, original_useCost_inr, ih]

/-- Structural instrumentation preserves the original operation/query static count exactly.
The unprojected static count still contains all structural and address-evaluation work. -/
theorem original_stmtCost_instrument (s : Stmt Op Tst) (idx : List ℕ) :
    Count.original (stmtCost s.instrument idx) = stmtCost s idx := by
  induction s generalizing idx with
  | skip => exact original_stmtCost_tally ..
  | abort => rfl
  | seq s t ihs iht =>
    simp [Stmt.instrument, stmtCost, original_stmtCost_tally, ihs, iht]
  | call o ds ins outs =>
    simp [Stmt.instrument, stmtCost, original_stmtCost_tally, original_useCost]
  | ite q ds ins t e iht ihe =>
    simp [Stmt.instrument, stmtCost, original_stmtCost_tally, Count.original_sup, iht, ihe,
      original_testCost]
  | whileFuel fuel q ds ins body k ih ihk =>
    simp [Stmt.instrument, stmtCost, original_stmtCost_tally, Count.original_finset_sup,
      ih, ihk, original_testCost]
  | bindIdx q ins bound body ih =>
    simp [Stmt.instrument, stmtCost, original_stmtCost_tally, Count.original_finset_sup, ih]
  | allocAs fmt len body ih =>
    simp [Stmt.instrument, stmtCost, original_stmtCost_tally, ih,
      original_useCost_inr]
  | loop n body ih =>
    simp [Stmt.instrument, stmtCost, original_stmtCost_tally, ih]
  | frame ds args body ih =>
    simp only [Stmt.instrument, stmtCost, map_add, original_stmtCost_tally, zero_add]
    cases IExp.evalList idx ds <;> cases IExp.evalList idx (args.map Operand.off) <;> simp [ih]

end NLAlib.Ops
