/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Logic.Writes
public import NLAlib.Ops.Catalog.Scalar

/-!
# Straight-line scalar blocks

A rotation, a norm, a coefficient update: a few dozen scalar instructions without loops or
branches. Under `IsScalar M I` (scalar arithmetic is the machine `M`, a total function on words)
their run is a fold of `M` over the cells, so the whole block is **one** specification: the
cells written, each with its value computed by `NLAlib.Ops.ScalarIns.evalBlock` on the cell
function of the store. The proof of a block is then one application of
`NLAlib.Ops.writes_scalarBlock` and one evaluation per output word (one `simp` over all outputs of
a long block is too slow: evaluate each output by its own lemma).

Success needs only that the cells read hold words when they are read (cells written earlier in
the block need no initialisation: the evaluation reads the updated cell function) and room for
the cells written; division is total in the machine, and its meaning at zero is the business of
the arithmetic contract (`StdModel.div`), not of the block.

## Main results

* `NLAlib.Ops.ScalarIns`, `NLAlib.Ops.Stmt.scalarBlock`, `NLAlib.Ops.ScalarIns.evalBlock`.
* `NLAlib.Ops.ScalarCall`, `NLAlib.Ops.IsScalar.scalarCall`: operations as functions of cells.
* `NLAlib.Ops.writes_scalarBlock`: the block rule, in total mode.
-/

@[expose] public section

namespace NLAlib.Ops

variable {Op Tst K : Type}

/-- A scalar instruction: an operation (of any tag) on cells. -/
structure ScalarIns (Op : Type) where
  /-- The operation, as a name of the signature (`Has.inj ScalarOp.add`, or the same at a tag). -/
  op : Op
  /-- The input cells. -/
  ins : List Operand
  /-- The output cell. -/
  out : Operand

/-- The call of one scalar instruction. -/
def ScalarIns.stmt (x : ScalarIns Op) : Stmt Op Tst := .call x.op [] x.ins [x.out]

/-- **A straight-line block** of scalar instructions, as a sequence of calls nested to the right.
The builder writes the calls themselves; they are this block by `rfl` at a literal list, which
the tactic of the rule states (`change`). -/
def Stmt.scalarBlock : List (ScalarIns Op) → Stmt Op Tst
  | [] => .skip
  | [x] => x.stmt
  | x :: xs => .seq x.stmt (Stmt.scalarBlock xs)

/-- The cells of a store as a function; `none` at a cell that holds no word. -/
def Store.cellFn (s : Store K) : ℕ × ℕ → Option K := fun z => s.get z.1 z.2

/-- The value of a scalar operation of the machine on the values of its inputs. -/
def Machine.eval (M : Machine K) : ScalarOp → List K → Option K
  | .lit q, [] => some (M.lit q)
  | .add, [a, b] => some (M.add a b)
  | .sub, [a, b] => some (M.sub a b)
  | .mul, [a, b] => some (M.mul a b)
  | .div, [a, b] => some (M.div a b)
  | .neg, [a] => some (M.neg a)
  | .sqrt, [a] => some (M.sqrt a)
  | .copy, [a] => some a
  | _, _ => none

/-- **A scalar operation as a function of cells**: a call of `o` with no dimensions on live
input cells holding `vs` and an output cell in bounds writes `g vs` in the output cell, when
`g vs` is defined. A total-mode property (the catalog's contracts are total). -/
def ScalarCall (I : Interp Op Tst K) (o : Op) (g : List K → Option K) : Prop :=
  ∀ (ins : List (ℕ × ℕ)) (z : ℕ × ℕ) (τ : Tape K) (m : Mem K) (vs : List K) (v : K),
    m.Live (ins ++ [z]) → ins.mapM (fun a => m.store.get a.1 a.2) = some vs →
    z.2 < m.store.len z.1 → g vs = some v → I.callS o [] ins [z] τ m = some (m.upd z v)

theorem mapM_cons_eq_some {α : Type} {f : α → Option K} {x : α} {l : List α} {vs : List K} :
    (x :: l).mapM f = some vs ↔ ∃ v vs', f x = some v ∧ l.mapM f = some vs' ∧ vs = v :: vs' := by
  rw [List.mapM_cons]
  cases hx : f x <;> cases hl : l.mapM f <;> simp [eq_comm]

theorem mapM_nil_eq_some {α : Type} {f : α → Option K} {vs : List K} :
    ([] : List α).mapM f = some vs ↔ vs = [] := by simp [eq_comm]

/-- The cells read hold words, so their buffers are live. -/
theorem live_of_mapM {m : Mem K} {ins : List (ℕ × ℕ)} {vs : List K}
    (h : ins.mapM (fun a => m.store.get a.1 a.2) = some vs) : m.Live ins := by
  induction ins generalizing vs with
  | nil => simp
  | cons x ins ih =>
    obtain ⟨v, vs', hv, hvs, rfl⟩ := mapM_cons_eq_some.mp h
    exact (Mem.live_cons _ _ _).mpr ⟨Store.lt_length_of_get hv, ih hvs⟩

/-- The scalar contract of the catalog, at any tag, as functions of cells. -/
theorem IsScalar.scalarCall [Has ScalarOp Op] {M : Machine K} {I : Interp Op Tst K}
    (hS : IsScalar M I) (a : ScalarOp) : ScalarCall I (Has.inj a) (M.eval a) := by
  intro ins z τ m vs v _ hvs hz hg
  refine (hS a).callS_eq (d := []) (ins := ins) (outs := [z]) trivial ?_
  rcases ins with _ | ⟨x, _ | ⟨y, _ | ⟨w, ins⟩⟩⟩
  · obtain rfl := mapM_nil_eq_some.mp hvs
    cases a <;> simp only [Machine.eval, reduceCtorEq, Option.some.injEq] at hg
    subst hg
    exact BlockFn.apply_const_eq_some_iff.mpr ⟨hz, rfl⟩
  · obtain ⟨u, vs', hu, hvs', rfl⟩ := mapM_cons_eq_some.mp hvs
    obtain rfl := mapM_nil_eq_some.mp hvs'
    cases a <;> simp only [Machine.eval, reduceCtorEq, Option.some.injEq] at hg <;> subst hg <;>
      exact BlockFn.apply_un_eq_some_iff.mpr ⟨u, _, hu, rfl, hz, rfl⟩
  · obtain ⟨u, vs', hu, hvs', rfl⟩ := mapM_cons_eq_some.mp hvs
    obtain ⟨u', vs'', hu', hvs'', rfl⟩ := mapM_cons_eq_some.mp hvs'
    obtain rfl := mapM_nil_eq_some.mp hvs''
    cases a <;> simp only [Machine.eval, reduceCtorEq, Option.some.injEq] at hg <;> subst hg <;>
      exact BlockFn.apply_bin_eq_some_iff.mpr ⟨u, u', _, hu, hu', rfl, hz, rfl⟩
  · obtain ⟨u, vs', hu, hvs', rfl⟩ := mapM_cons_eq_some.mp hvs
    obtain ⟨u', vs'', hu', hvs'', rfl⟩ := mapM_cons_eq_some.mp hvs'
    obtain ⟨u'', vs''', hu'', hvs''', rfl⟩ := mapM_cons_eq_some.mp hvs''
    cases a <;> simp [Machine.eval] at hg

/-- **The evaluation of a block** on a cell function, given the function `sem` of each operation:
the cells written, in order, with their values; each instruction reads the cells as updated by
the instructions before it. `none` if an operand does not evaluate, a cell read holds no word or
`sem` is undefined. -/
def ScalarIns.evalBlock (sem : Op → List K → Option K) (ρ : Env) :
    List (ScalarIns Op) → (ℕ × ℕ → Option K) → Option (List ((ℕ × ℕ) × K))
  | [], _ => some []
  | x :: xs, f =>
    (Operand.evalList ρ x.ins).bind fun a => (a.mapM f).bind fun vs => (x.out.eval ρ).bind
      fun z => (sem x.op vs).bind fun v =>
        (ScalarIns.evalBlock sem ρ xs (Function.update f z (some v))).map fun ws => (z, v) :: ws

/-- Write the cells `ws`, in order. -/
def Mem.updCells (m : Mem K) : List ((ℕ × ℕ) × K) → Mem K
  | [] => m
  | w :: ws => (m.upd w.1 w.2).updCells ws

/-- **The block rule** (total mode): a straight-line block of scalar instructions whose
operations are functions of cells (`ScalarCall`, e.g. by `IsScalar.scalarCall`, at any tag or
mixing tags) writes its output cells, and the memory after it is the memory before with the
evaluated cells written. It needs room for the cells written and live input cells (the cells
read hold words: that is the evaluation succeeding).

Only total mode: the catalog's scalar contracts are total, and a total contract says nothing of
a call outside its precondition, so a liberal statement would need the room anyway. A block that
contains catalog calls gets its liberal corollary by `Writes.of_total`, under the same
hypotheses; one proof does not give both modes for free. -/
theorem writes_scalarBlock {I : Interp Op Tst K} {τ : Tape K} {ρ : Env} {m : Mem K}
    {sem : Op → List K → Option K} {xs : List (ScalarIns Op)}
    (hS : ∀ x ∈ xs, ScalarCall I x.op (sem x.op)) {ws : List ((ℕ × ℕ) × K)}
    (hev : ScalarIns.evalBlock sem ρ xs m.store.cellFn = some ws)
    (hroom : ∀ w ∈ ws, w.1.2 < m.store.len w.1.1) :
    Writes .total I τ (Stmt.scalarBlock xs) ρ (Fp.cells (ws.map Prod.fst))
      (fun m' => m' = m.updCells ws) m := by
  suffices key : ∀ (m : Mem K) (ws : List ((ℕ × ℕ) × K)),
      ScalarIns.evalBlock sem ρ xs m.store.cellFn = some ws →
      (∀ w ∈ ws, w.1.2 < m.store.len w.1.1) →
      eval I τ (Stmt.scalarBlock xs) ρ m = some (m.updCells ws) ∧
        m.store.EqOff (Fp.cells (ws.map Prod.fst)) (m.updCells ws).store from
    wp_of_run (key m ws hev hroom).1 ⟨(key m ws hev hroom).2, rfl⟩
  clear hev hroom ws m
  induction xs with
  | nil =>
    intro m ws hev _
    simp only [ScalarIns.evalBlock, Option.some.injEq] at hev
    subst hev
    exact ⟨rfl, Store.EqOff.refl _ _⟩
  | cons x xs ih =>
    intro m ws hev hroom
    simp only [ScalarIns.evalBlock] at hev
    obtain ⟨a, ha, hev⟩ := Option.bind_eq_some_iff.mp hev
    obtain ⟨vs, hvs, hev⟩ := Option.bind_eq_some_iff.mp hev
    obtain ⟨z, hz, hev⟩ := Option.bind_eq_some_iff.mp hev
    obtain ⟨v, hv, hev⟩ := Option.bind_eq_some_iff.mp hev
    obtain ⟨ws', hws', rfl⟩ := Option.map_eq_some_iff.mp hev
    have hzl : z.2 < m.store.len z.1 := hroom (z, v) (by simp)
    have hcall : I.callS x.op [] a [z] τ m = some (m.upd z v) :=
      hS x (by simp) a z τ m vs v ((Mem.live_append _ _ _).mpr ⟨live_of_mapM hvs,
        by simpa using Store.lt_length_of_lt_len hzl⟩) hvs hzl hv
    have hcell : (m.upd z v).store.cellFn = Function.update m.store.cellFn z (some v) := by
      funext y
      by_cases hy : y = z
      · subst hy
        simp [Store.cellFn, Store.get_upd_self hzl]
      · rw [Function.update_of_ne hy]
        simp only [Store.cellFn, Mem.store_upd]
        exact Store.get_upd_of_ne (by
          by_contra hc
          push Not at hc
          exact hy (Prod.ext hc.1 hc.2)) v
    have hrun1 : eval I τ x.stmt ρ m = some (m.upd z v) := by
      simp [ScalarIns.stmt, eval, ha, Operand.evalList, hz, hcall]
    obtain ⟨hrun, hfr⟩ := ih (fun y hy => hS y (by simp [hy])) (m.upd z v) ws'
      (by rw [hcell]; exact hws') fun w hw => by
        simpa using hroom w (by simp [hw])
    refine ⟨?_, ?_⟩
    · cases xs with
      | nil =>
        simp only [ScalarIns.evalBlock, Option.some.injEq] at hws'
        subst hws'
        exact hrun1
      | cons y ys =>
        change (eval I τ x.stmt ρ m).bind (eval I τ (Stmt.scalarBlock (y :: ys)) ρ) = _
        rw [hrun1, Option.bind_some, hrun]
        rfl
    · refine ((Store.EqOff.refl _ _).upd (show Fp.cells _ z.1 z.2 by simp [Fp.cells]) v).trans
        (hfr.mono fun b i h => ?_)
      simp only [Fp.cells, List.map_cons, List.mem_cons] at h ⊢
      exact Or.inr h

/-- A cell not written by the block keeps its value. -/
theorem get_updCells_of_notMem {m : Mem K} {ws : List ((ℕ × ℕ) × K)} {z : ℕ × ℕ}
    (hz : z ∉ ws.map Prod.fst) : (m.updCells ws).store.get z.1 z.2 = m.store.get z.1 z.2 := by
  induction ws generalizing m with
  | nil => rfl
  | cons w ws ih =>
    simp only [List.map_cons, List.mem_cons, not_or] at hz
    simp only [Mem.updCells]
    rw [ih hz.2]
    simp only [Mem.store_upd]
    exact Store.get_upd_of_ne (by
      by_contra hc
      exact hz.1 (Prod.ext (not_not.mp (not_or.mp hc).1) (not_not.mp (not_or.mp hc).2))) _

/-- Writing a list of cells in two parts. -/
theorem updCells_append (m : Mem K) (ws₁ ws₂ : List ((ℕ × ℕ) × K)) :
    m.updCells (ws₁ ++ ws₂) = (m.updCells ws₁).updCells ws₂ := by
  induction ws₁ generalizing m with
  | nil => rfl
  | cons w ws ih => exact ih _

theorem len_updCells (m : Mem K) (ws : List ((ℕ × ℕ) × K)) (b : ℕ) :
    (m.updCells ws).store.len b = m.store.len b := by
  induction ws generalizing m with
  | nil => rfl
  | cons w ws ih => rw [Mem.updCells, ih]; simp

/-- **The value of a cell after the block**: the last value written to it (one lemma per output
word, not one `simp` over the whole block). -/
theorem get_updCells {m : Mem K} {ws₁ ws₂ : List ((ℕ × ℕ) × K)} {z : ℕ × ℕ} {v : K}
    (hl : z.2 < m.store.len z.1) (hz : z ∉ ws₂.map Prod.fst) :
    (m.updCells (ws₁ ++ (z, v) :: ws₂)).store.get z.1 z.2 = some v := by
  rw [updCells_append, Mem.updCells, get_updCells_of_notMem hz]
  simp only [Mem.store_upd]
  exact Store.get_upd_self (by rw [len_updCells]; exact hl) v

end NLAlib.Ops
