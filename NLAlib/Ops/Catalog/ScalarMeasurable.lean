/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.MeasureTheory.Function.Floor
public import NLAlib.Ops.Catalog.Compare
public import NLAlib.Ops.Catalog.Index
public import NLAlib.Ops.Logic.Probabilistic

/-!
# Measurable catalog operations

`NLAlib.Ops.Interp.IsMeasurable` asks that every call, test and index of an interpretation be
measurable in the tape and the memory, everywhere: also off the operands and memories that the
catalog contracts (`NLAlib.Ops.IsScalar`, `NLAlib.Ops.IsCmp`, …) speak about, where a contract
leaves the interpretation free. So a contract does not give measurability; the **canonical**
meanings do. This file states measurability at the level of block functions
(`NLAlib.Ops.BlockFn.MeasurableApply`), so that it applies to every interpretation built by
`NLAlib.Ops.Interp.ofFns` over any operation type, and assembles an interpretation from its
operations, tests and indices (`NLAlib.Ops.Interp.isMeasurable_of_calls`).

## Main definitions

* `NLAlib.Ops.Machine.IsMeasurable`, `NLAlib.Ops.BlockFn.MeasurableApply`,
  `NLAlib.Ops.Interp.IsMeasurableCall`, `NLAlib.Ops.Interp.IsMeasurableTest`,
  `NLAlib.Ops.Interp.IsMeasurableIndex`.

## Main results

* `NLAlib.Ops.Interp.isMeasurable_of_calls`: the assembly over all operations.
* `NLAlib.Ops.BlockFn.measurableApply_const`, `.measurableApply_un`, `.measurableApply_bin`.
* `NLAlib.Ops.Machine.IsMeasurable.measurableApply_fn`: each scalar operation of a measurable
  machine; `NLAlib.Ops.Machine.measurableApply_indexFn`: the dimension literal.
* `NLAlib.Ops.CmpTst.isMeasurableTest`, `NLAlib.Ops.isMeasurableIndex_toNat`: the canonical
  comparisons and conversion of a measurable decoding.
-/

@[expose] public section

open MeasureTheory

namespace NLAlib.Ops

variable {K Op Tst : Type}

/-- **A measurable machine**: its binary word functions are measurable on pairs and its unary
word functions are measurable, on every word (division by zero included). Literals are
constants. -/
structure Machine.IsMeasurable [MeasurableSpace K] (M : Machine K) : Prop where
  /-- Addition. -/
  add : Measurable fun x : K × K => M.add x.1 x.2
  /-- Subtraction. -/
  sub : Measurable fun x : K × K => M.sub x.1 x.2
  /-- Multiplication. -/
  mul : Measurable fun x : K × K => M.mul x.1 x.2
  /-- Division. -/
  div : Measurable fun x : K × K => M.div x.1 x.2
  /-- Negation. -/
  neg : Measurable M.neg
  /-- Square root. -/
  sqrt : Measurable M.sqrt

variable [Inhabited K] [MeasurableSpace K]

/-- **A block function with a measurable effect**: at all dimensions and operands its effect on
the memory is a measurable step. -/
def BlockFn.MeasurableApply (f : BlockFn K) : Prop :=
  ∀ d ins outs, MeasurableRun (f.apply d ins outs)

/-- **A measurable operation** of an interpretation: at all dimensions and operands, its call is a
measurable step. -/
def Interp.IsMeasurableCall (I : Interp Op Tst K) (o : Op) : Prop :=
  ∀ d ins outs, MeasurableRun (I.call o d ins outs)

/-- **A measurable test**: its success flag and its value are measurable in the memory. -/
def Interp.IsMeasurableTest (I : Interp Op Tst K) (q : Tst) : Prop :=
  ∀ d ins, Measurable (fun m : Mem K => (I.test q d ins m).isSome) ∧
    Measurable (fun m : Mem K => (I.test q d ins m).getD false)

/-- **A measurable index**: its success flag and its value are measurable in the memory. -/
def Interp.IsMeasurableIndex (I : Interp Op Tst K) (q : Tst) : Prop :=
  ∀ ins, Measurable (fun m : Mem K => (I.index q ins m).isSome) ∧
    Measurable (fun m : Mem K => (I.index q ins m).getD 0)

/-- The operations of `Interp.ofFns F` are measurable exactly when their block functions are. -/
theorem Interp.ofFns_isMeasurableCall (F : Op → BlockFn K) (o : Op) :
    (Interp.ofFns F : Interp Op Tst K).IsMeasurableCall o ↔ (F o).MeasurableApply :=
  Iff.rfl

/-- **Assembly** (PL4): an interpretation whose operations, tests and indices are measurable is
measurable. -/
theorem Interp.isMeasurable_of_calls {I : Interp Op Tst K} (hc : ∀ o, I.IsMeasurableCall o)
    (ht : ∀ q, I.IsMeasurableTest q) (hi : ∀ q, I.IsMeasurableIndex q) : I.IsMeasurable :=
  ⟨fun o d ins outs => hc o d ins outs, fun q d ins => ht q d ins, fun q ins => hi q ins⟩

/-! ### Block functions of cells -/

/-- A step that succeeds exactly on a measurable set of memories, with a measurable result, is
measurable. -/
theorem MeasurableRun.of_iff {f : Tape K → Mem K → Option (Mem K)} {C : Mem K → Prop}
    {g : Mem K → Mem K} (hC : MeasurableSet {m | C m}) (hg : Measurable g)
    (he : ∀ τ m m', f τ m = some m' ↔ C m ∧ m' = g m) : MeasurableRun f := by
  classical
  have e : f = fun τ m => if C m then some (g ((τ, m) : Tape K × Mem K).2) else none := by
    funext τ m
    by_cases hc : C m
    · rw [if_pos hc]
      exact (he τ m _).mpr ⟨hc, rfl⟩
    · rw [if_neg hc]
      exact Option.eq_none_iff_forall_ne_some.mpr fun m' h => hc ((he τ m m').mp h).1
  rw [e]
  exact MeasurableRun.guard (p := fun _ m => C m) (g := fun x => g x.2) (measurable_snd hC)
    (hg.comp measurable_snd)

/-- A step that never succeeds is measurable. -/
theorem MeasurableRun.of_forall_ne {f : Tape K → Mem K → Option (Mem K)}
    (h : ∀ τ m m', f τ m ≠ some m') : MeasurableRun f := by
  have e : f = fun _ _ => none := funext₂ fun τ m =>
    Option.eq_none_iff_forall_ne_some.mpr (h τ m)
  rw [e]
  exact MeasurableRun.none_mem

theorem Mem.measurableSet_get_isSome (x : ℕ × ℕ) :
    MeasurableSet {m : Mem K | (m.store.get x.1 x.2).isSome = true} :=
  (measurable_fst.comp (Mem.measurable_cell x)) (measurableSet_singleton true)

theorem Mem.measurable_get_getD (x : ℕ × ℕ) :
    Measurable fun m : Mem K => (m.store.get x.1 x.2).getD default :=
  measurable_snd.comp (Mem.measurable_cell x)

theorem Mem.measurableSet_room_one (z : ℕ × ℕ) :
    MeasurableSet {m : Mem K | z.2 + 1 ≤ m.store.len z.1} :=
  Mem.measurable_len z.1 (MeasurableSet.of_discrete (s := {k | z.2 + 1 ≤ k}))

omit [Inhabited K] [MeasurableSpace K] in
/-- The room for one output cell fails for any other list of outputs. -/
theorem Mem.not_room_one {m : Mem K} {outs : List (ℕ × ℕ)} (h : ∀ z, outs ≠ [z]) :
    ¬ m.Room outs [1] := by
  rcases outs with _ | ⟨z, _ | ⟨z', outs⟩⟩
  · simp [Mem.Room]
  · exact absurd rfl (h z)
  · simp [Mem.Room]

/-- **A constant** writes a fixed word: measurable. -/
theorem BlockFn.measurableApply_const (v : K) : (BlockFn.const v).MeasurableApply := by
  intro d ins outs
  by_cases hs : ins = [] ∧ ∃ z, outs = [z]
  · obtain ⟨rfl, z, rfl⟩ := hs
    refine MeasurableRun.of_iff (C := fun m => d.length = 0 ∧ m.Live [z] ∧
      z.2 + 1 ≤ m.store.len z.1) (g := fun m => m.upd z v)
      ((MeasurableSet.const _).inter ((Mem.measurableSet_live _).inter
        (Mem.measurableSet_room_one z)))
      ((Mem.measurable_upd z).comp (measurable_id.prodMk measurable_const)) fun τ m m' => ?_
    rw [BlockFn.apply_eq_some_iff]
    simp [Mem.updBlock_singleton]
    tauto
  · refine MeasurableRun.of_forall_ne fun τ m m' h => hs ?_
    obtain ⟨-, -, xs, ys, hxs, hys, -, hroom, -⟩ := BlockFn.apply_eq_some_iff.mp h
    refine ⟨?_, ?_⟩
    · rcases ins with _ | ⟨x, ins⟩
      · rfl
      · simp [Mem.readBlocks] at hxs
    · by_contra hz
      exact Mem.not_room_one (fun z e => hz ⟨z, e⟩) (by simpa using hroom)

/-- **A function of one cell** with a measurable success flag and value: measurable. -/
theorem BlockFn.measurableApply_un {g : K → Option K} (hg₁ : Measurable fun a => (g a).isSome)
    (hg₂ : Measurable fun a => (g a).getD default) : (BlockFn.un g).MeasurableApply := by
  intro d ins outs
  by_cases hs : ∃ x z, ins = [x] ∧ outs = [z]
  · obtain ⟨x, z, rfl, rfl⟩ := hs
    have hv := Mem.measurable_get_getD (K := K) x
    refine MeasurableRun.of_iff (C := fun m => d.length = 0 ∧ m.Live [x, z] ∧
      (m.store.get x.1 x.2).isSome ∧ (g ((m.store.get x.1 x.2).getD default)).isSome ∧
        z.2 + 1 ≤ m.store.len z.1)
      (g := fun m => m.upd z ((g ((m.store.get x.1 x.2).getD default)).getD default))
      ((MeasurableSet.const _).inter ((Mem.measurableSet_live _).inter
        ((Mem.measurableSet_get_isSome x).inter
          (((hg₁.comp hv) (measurableSet_singleton true)).inter
            (Mem.measurableSet_room_one z)))))
      ((Mem.measurable_upd z).comp (measurable_id.prodMk (hg₂.comp hv))) fun τ m m' => ?_
    rw [BlockFn.apply_eq_some_iff]
    rcases hx : m.store.get x.1 x.2 with _ | a
    · simp [BlockFn.readBlocks_cells_one, hx]
    rcases hg : g a with _ | w <;>
      simp [BlockFn.readBlocks_cells_one, hx, hg, Mem.updBlock_singleton]
    tauto
  · refine MeasurableRun.of_forall_ne fun τ m m' h => hs ?_
    obtain ⟨-, -, xs, ys, hxs, hys, -, hroom, -⟩ := BlockFn.apply_eq_some_iff.mp h
    have hz : ∃ z, outs = [z] := by
      by_contra hz
      exact Mem.not_room_one (fun z e => hz ⟨z, e⟩) (by simpa using hroom)
    obtain ⟨z, rfl⟩ := hz
    rcases ins with _ | ⟨x, _ | ⟨y, ins⟩⟩
    · simp [Mem.readBlocks] at hxs
    · exact ⟨x, z, rfl, rfl⟩
    · simp [Mem.readBlocks] at hxs

/-- **A function of two cells** with a measurable success flag and value: measurable. -/
theorem BlockFn.measurableApply_bin {g : K → K → Option K}
    (hg₁ : Measurable fun p : K × K => (g p.1 p.2).isSome)
    (hg₂ : Measurable fun p : K × K => (g p.1 p.2).getD default) :
    (BlockFn.bin g).MeasurableApply := by
  intro d ins outs
  by_cases hs : ∃ x y z, ins = [x, y] ∧ outs = [z]
  · obtain ⟨x, y, z, rfl, rfl⟩ := hs
    have hv := (Mem.measurable_get_getD (K := K) x).prodMk (Mem.measurable_get_getD (K := K) y)
    refine MeasurableRun.of_iff (C := fun m => d.length = 0 ∧ m.Live [x, y, z] ∧
      (m.store.get x.1 x.2).isSome ∧ (m.store.get y.1 y.2).isSome ∧
      (g ((m.store.get x.1 x.2).getD default) ((m.store.get y.1 y.2).getD default)).isSome ∧
        z.2 + 1 ≤ m.store.len z.1)
      (g := fun m => m.upd z
        ((g ((m.store.get x.1 x.2).getD default) ((m.store.get y.1 y.2).getD default)).getD
          default))
      ((MeasurableSet.const _).inter ((Mem.measurableSet_live _).inter
        ((Mem.measurableSet_get_isSome x).inter ((Mem.measurableSet_get_isSome y).inter
          (((hg₁.comp hv) (measurableSet_singleton true)).inter
            (Mem.measurableSet_room_one z))))))
      ((Mem.measurable_upd z).comp (measurable_id.prodMk (hg₂.comp hv))) fun τ m m' => ?_
    rw [BlockFn.apply_eq_some_iff]
    rcases hx : m.store.get x.1 x.2 with _ | a
    · simp [BlockFn.readBlocks_cells_two, hx]
    rcases hy : m.store.get y.1 y.2 with _ | b
    · simp [BlockFn.readBlocks_cells_two, hx, hy]
    rcases hg : g a b with _ | w <;>
      simp [BlockFn.readBlocks_cells_two, hx, hy, hg, Mem.updBlock_singleton]
    tauto
  · refine MeasurableRun.of_forall_ne fun τ m m' h => hs ?_
    obtain ⟨-, -, xs, ys, hxs, hys, -, hroom, -⟩ := BlockFn.apply_eq_some_iff.mp h
    have hz : ∃ z, outs = [z] := by
      by_contra hz
      exact Mem.not_room_one (fun z e => hz ⟨z, e⟩) (by simpa using hroom)
    obtain ⟨z, rfl⟩ := hz
    rcases ins with _ | ⟨x, _ | ⟨y, _ | ⟨w, ins⟩⟩⟩
    · simp [Mem.readBlocks] at hxs
    · simp [Mem.readBlocks] at hxs
    · exact ⟨x, y, z, rfl, rfl⟩
    · simp [Mem.readBlocks] at hxs

/-- **The scalar operations of a measurable machine** (PL4): each block function is measurable. -/
theorem Machine.IsMeasurable.measurableApply_fn {M : Machine K} (hM : M.IsMeasurable)
    (a : ScalarOp) : (M.fn a).MeasurableApply := by
  cases a with
  | lit q => exact BlockFn.measurableApply_const _
  | add => exact BlockFn.measurableApply_bin measurable_const hM.add
  | sub => exact BlockFn.measurableApply_bin measurable_const hM.sub
  | mul => exact BlockFn.measurableApply_bin measurable_const hM.mul
  | div => exact BlockFn.measurableApply_bin measurable_const hM.div
  | neg => exact BlockFn.measurableApply_un measurable_const hM.neg
  | sqrt => exact BlockFn.measurableApply_un measurable_const hM.sqrt
  | copy => exact BlockFn.measurableApply_un measurable_const measurable_id

/-- **The dimension literal** (PL4) is measurable, for every machine: it writes a word that
depends on the dimension only. -/
theorem Machine.measurableApply_indexFn (M : Machine K) : M.indexFn.MeasurableApply := by
  intro d ins outs
  by_cases hs : ins = [] ∧ ∃ z, outs = [z]
  · obtain ⟨rfl, z, rfl⟩ := hs
    refine MeasurableRun.of_iff (C := fun m => d.length = 1 ∧ m.Live [z] ∧
      z.2 + 1 ≤ m.store.len z.1) (g := fun m => m.upd z (M.lit (d.headD 0)))
      ((MeasurableSet.const _).inter ((Mem.measurableSet_live _).inter
        (Mem.measurableSet_room_one z)))
      ((Mem.measurable_upd z).comp (measurable_id.prodMk measurable_const)) fun τ m m' => ?_
    rw [BlockFn.apply_eq_some_iff]
    simp [Machine.indexFn, Mem.updBlock_singleton]
    tauto
  · refine MeasurableRun.of_forall_ne fun τ m m' h => hs ?_
    obtain ⟨-, -, xs, ys, hxs, hys, -, hroom, -⟩ := BlockFn.apply_eq_some_iff.mp h
    refine ⟨?_, ?_⟩
    · rcases ins with _ | ⟨x, ins⟩
      · rfl
      · simp [Machine.indexFn, Mem.readBlocks] at hxs
    · by_contra hz
      exact Mem.not_room_one (fun z e => hz ⟨z, e⟩) (by simpa [Machine.indexFn] using hroom)

/-! ### Tests and indices of cells -/

omit [Inhabited K] [MeasurableSpace K] in
/-- Reading blocks fails when the number of operands is not the number of lengths. -/
theorem Mem.readBlocks_eq_none_of_length_ne {m : Mem K} :
    ∀ {as : List (ℕ × ℕ)} {ns : List ℕ}, as.length ≠ ns.length → m.readBlocks as ns = none
  | [], [], h => absurd rfl h
  | [], _ :: _, _ => rfl
  | _ :: _, [], _ => rfl
  | a :: as, n :: ns, h => by
    rw [Mem.readBlocks_cons, Mem.readBlocks_eq_none_of_length_ne (by simpa using h)]
    cases m.store.readBlock a.1 a.2 n <;> rfl

/-- A Boolean of one cell read from the memory, measurable on the cell: measurable. -/
theorem Mem.measurable_readBlocks_one_map {x : ℕ × ℕ} {φ : List (List K) → Bool}
    (hφ : MeasurableSet {a : K | φ [[a]] = true}) :
    Measurable (fun m : Mem K => ((m.readBlocks [x] [1]).map φ).isSome) ∧
      Measurable (fun m : Mem K => ((m.readBlocks [x] [1]).map φ).getD false) := by
  have hv := Mem.measurable_get_getD (K := K) x
  refine ⟨?_, ?_⟩
  · convert Measurable.ite (p := fun m : Mem K => (m.store.get x.1 x.2).isSome = true)
      (Mem.measurableSet_get_isSome (K := K) x)
      (measurable_const (a := true)) (measurable_const (a := false)) using 1
    · funext m
      simp only [BlockFn.readBlocks_cell_cons, Mem.readBlocks_nil]
      rcases Option.eq_none_or_eq_some (m.store.get x.1 x.2) with h | ⟨a, h⟩ <;> simp [h]
    · exact fun _ => inferInstance
  · classical
    convert Measurable.ite (p := fun m : Mem K => (m.store.get x.1 x.2).isSome = true ∧
      φ [[(m.store.get x.1 x.2).getD default]] = true)
      ((Mem.measurableSet_get_isSome (K := K) x).inter (hv hφ))
      (measurable_const (a := true)) (measurable_const (a := false)) using 1
    · funext m
      simp only [BlockFn.readBlocks_cell_cons, Mem.readBlocks_nil]
      rcases Option.eq_none_or_eq_some (m.store.get x.1 x.2) with h | ⟨a, h⟩ <;> simp [h]
    · exact fun _ => inferInstance

/-- A Boolean of two cells read from the memory, measurable on the pair: measurable. -/
theorem Mem.measurable_readBlocks_two_map {x y : ℕ × ℕ} {φ : List (List K) → Bool}
    (hφ : MeasurableSet {p : K × K | φ [[p.1], [p.2]] = true}) :
    Measurable (fun m : Mem K => ((m.readBlocks [x, y] [1, 1]).map φ).isSome) ∧
      Measurable (fun m : Mem K => ((m.readBlocks [x, y] [1, 1]).map φ).getD false) := by
  classical
  have hv := (Mem.measurable_get_getD (K := K) x).prodMk (Mem.measurable_get_getD (K := K) y)
  refine ⟨?_, ?_⟩
  · convert Measurable.ite (p := fun m : Mem K => (m.store.get x.1 x.2).isSome = true ∧
      (m.store.get y.1 y.2).isSome = true)
      ((Mem.measurableSet_get_isSome (K := K) x).inter (Mem.measurableSet_get_isSome (K := K) y))
      (measurable_const (a := true)) (measurable_const (a := false)) using 1
    · funext m
      simp only [BlockFn.readBlocks_cell_cons, Mem.readBlocks_nil]
      rcases Option.eq_none_or_eq_some (m.store.get x.1 x.2) with h | ⟨a, h⟩ <;>
        rcases Option.eq_none_or_eq_some (m.store.get y.1 y.2) with h' | ⟨b, h'⟩ <;> simp [h, h']
    · exact fun _ => inferInstance
  · convert Measurable.ite (p := fun m : Mem K => (m.store.get x.1 x.2).isSome = true ∧
      (m.store.get y.1 y.2).isSome = true ∧
      φ [[(m.store.get x.1 x.2).getD default], [(m.store.get y.1 y.2).getD default]] = true)
      ((Mem.measurableSet_get_isSome (K := K) x).inter
        ((Mem.measurableSet_get_isSome (K := K) y).inter (hv hφ)))
      (measurable_const (a := true)) (measurable_const (a := false)) using 1
    · funext m
      simp only [BlockFn.readBlocks_cell_cons, Mem.readBlocks_nil]
      rcases Option.eq_none_or_eq_some (m.store.get x.1 x.2) with h | ⟨a, h⟩ <;>
        rcases Option.eq_none_or_eq_some (m.store.get y.1 y.2) with h' | ⟨b, h'⟩ <;> simp [h, h']
    · exact fun _ => inferInstance

/-- **The canonical comparisons** (PL4): a test that is a comparison of a measurable decoding of
the cells it reads is measurable. -/
theorem CmpTst.isMeasurableTest {I : Interp Op Tst K} {q : Tst} {dec : K → ℝ}
    (hdec : Measurable dec) (c : CmpTst)
    (hq : ∀ d a m, I.test q d a m = (m.readBlocks a c.lens).map (c.fn dec)) :
    I.IsMeasurableTest q := by
  intro d a
  simp only [hq]
  by_cases hl : a.length = c.lens.length
  · cases c with
    | lt =>
      obtain ⟨x, y, rfl⟩ := List.length_eq_two.mp hl
      exact Mem.measurable_readBlocks_two_map (by
        simp only [CmpTst.fn, decide_eq_true_eq]
        exact measurableSet_lt (hdec.comp measurable_fst) (hdec.comp measurable_snd))
    | le =>
      obtain ⟨x, y, rfl⟩ := List.length_eq_two.mp hl
      exact Mem.measurable_readBlocks_two_map (by
        simp only [CmpTst.fn, decide_eq_true_eq]
        exact measurableSet_le (hdec.comp measurable_fst) (hdec.comp measurable_snd))
    | eq =>
      obtain ⟨x, y, rfl⟩ := List.length_eq_two.mp hl
      exact Mem.measurable_readBlocks_two_map (by
        simp only [CmpTst.fn, decide_eq_true_eq]
        exact measurableSet_eq_fun (hdec.comp measurable_fst) (hdec.comp measurable_snd))
    | isZero =>
      obtain ⟨x, rfl⟩ := List.length_eq_one_iff.mp hl
      exact Mem.measurable_readBlocks_one_map (by
        simp only [CmpTst.fn, decide_eq_true_eq]
        exact hdec (measurableSet_singleton 0))
    | isPos =>
      obtain ⟨x, rfl⟩ := List.length_eq_one_iff.mp hl
      exact Mem.measurable_readBlocks_one_map (by
        simp only [CmpTst.fn, decide_eq_true_eq]
        exact measurableSet_lt measurable_const hdec)
  · simp only [Mem.readBlocks_eq_none_of_length_ne hl, Option.map_none]
    exact ⟨measurable_const, measurable_const⟩

/-- **The canonical conversion to an index** (PL4): an index that is the floor of a nonnegative
measurable decoding of the cell it reads is measurable. -/
theorem isMeasurableIndex_toNat {I : Interp Op Tst K} {q : Tst} {dec : K → ℝ}
    (hdec : Measurable dec)
    (hq : ∀ a m, I.index q a m =
      (m.readBlocks a (a.map fun _ => 1)).bind fun xs => toNatFn dec xs.flatten) :
    I.IsMeasurableIndex q := by
  intro a
  simp only [hq]
  rcases a with _ | ⟨z, _ | ⟨y, a⟩⟩
  · simp [toNatFn]
  · classical
    have hv := Mem.measurable_get_getD (K := K) z
    have hS : MeasurableSet {m : Mem K | (m.store.get z.1 z.2).isSome = true ∧
        0 ≤ dec ((m.store.get z.1 z.2).getD default)} :=
      (Mem.measurableSet_get_isSome z).inter (measurableSet_le measurable_const (hdec.comp hv))
    refine ⟨?_, ?_⟩
    · convert Measurable.ite (p := fun m : Mem K => (m.store.get z.1 z.2).isSome = true ∧
        0 ≤ dec ((m.store.get z.1 z.2).getD default)) hS (measurable_const (a := true))
        (measurable_const (a := false)) using 1
      · funext m
        simp only [List.map_cons, List.map_nil, BlockFn.readBlocks_cell_cons, Mem.readBlocks_nil]
        rcases Option.eq_none_or_eq_some (m.store.get z.1 z.2) with h | ⟨w, h⟩ <;> simp [h, toNatFn]
        split_ifs with hw <;> simp [hw]
      · exact fun _ => inferInstance
    · convert Measurable.ite (p := fun m : Mem K => (m.store.get z.1 z.2).isSome = true ∧
        0 ≤ dec ((m.store.get z.1 z.2).getD default)) hS
        (Nat.measurable_floor.comp (hdec.comp hv)) (measurable_const (a := 0)) using 1
      · funext m
        simp only [List.map_cons, List.map_nil, BlockFn.readBlocks_cell_cons, Mem.readBlocks_nil]
        rcases Option.eq_none_or_eq_some (m.store.get z.1 z.2) with h | ⟨w, h⟩ <;> simp [h, toNatFn]
        split_ifs <;> simp
      · exact fun _ => inferInstance
  · have h : ∀ m : Mem K, ((m.readBlocks (z :: y :: a) ((z :: y :: a).map fun _ => 1)).bind
        fun xs => toNatFn dec xs.flatten) = none := by
      intro m
      simp only [List.map_cons, BlockFn.readBlocks_cell_cons]
      cases m.store.get z.1 z.2 <;> cases m.store.get y.1 y.2 <;>
        cases m.readBlocks a (a.map fun _ => 1) <;> simp [toNatFn]
    simp only [h]
    exact ⟨measurable_const, measurable_const⟩

end NLAlib.Ops
