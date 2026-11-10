/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Catalog.Compare
public import NLAlib.Ops.Counted

/-!
# Fixture: a split whose sizes are read from the store, with weighted counts

`NLAlib.Ops.Examples.split o` reads a size `k₊ ≤ k` from a cell and calls the kernel `o` at the
sizes `k₊` and `k - k₊`. Its counts depend on the data. The static count charges the index
binder with every value up to its bound, so for a weight `T` it gives a sum over all splits; the
logic that carries the counts (`NLAlib.Ops.RunsFromW`) charges the value read.

## Main results

* `NLAlib.Ops.Examples.exists_isIdle_isToNat`: the contract set of the fixture can be met.
* `NLAlib.Ops.Examples.runsW_split`: the exact counts of one run, through `bindIdx` and `seq`.
* `NLAlib.Ops.Examples.weight_split_le`: for every superadditive `T`, the weighted count of the
  run is at most `T k`: `T k₊ + T (k - k₊) ≤ T k`. Tight, and for all `T` at once.
* `NLAlib.Ops.Examples.splitTable_accountsW`: the split as the implementation of a kernel
  `work [k]` over a lower kernel. Its counts are not a function of `(operation, dimensions)`, so
  it has no uniform accounting certificate with a tight cost; it has a weighted one
  (`NLAlib.Ops.Table.AccountsW`), with the weight `T k`.
* `NLAlib.Ops.Examples.runsW_twice_link`: an algorithm that calls `work [k]` twice, linked: the
  weighted count of the linked program is at most `2 T k`, by `NLAlib.Ops.exec_link_weight`.
-/

@[expose] public section

namespace NLAlib.Ops.Examples

open NLAlib.Ops

variable {K Op : Type}

/-- **The split**: read `k₊` from a cell, at most `k`; call the kernel `o` at `k₊` and at
`k - k₊`. Index variables: `k`, the offset of the cell, then `k₊`; buffer variable: the cell. -/
def split (o : Op) : Stmt Op IdxTst :=
  .bindIdx .toNat [⟨0, .var 1⟩] (.var 0)
    (.seq (.call o [.var 2] [] []) (.call o [.var 0 - .var 2] [] []))

/-- The contract of a kernel with no operand: it changes nothing. Only its count matters. -/
@[simps (attr := storeNF)]
def idleRel : BlockRel K where
  nd := 1
  inLens _ := []
  outLens _ := []
  rel _ _ _ ys := ys = []

/-- A call of an idle kernel. -/
theorem wp_idle {J : Interp Op IdxTst K} {o : Op}
    (hK : J.Meets .total o ((idleRel (K := K)).spec AnyOperands)) {τ : Tape K} {ρ : Env}
    {e : IExp} {n : ℕ} (he : e.eval ρ.idx = some n) {m : Mem K} :
    Wp .total J τ (.call o [e] [] []) ρ (· = m) m := by
  refine wp_call_rel hK (d := [n]) (a := []) (b := []) (by simp [he]) rfl rfl rfl rfl rfl trivial
    (by simp) rfl trivial trivial fun ys _ hys => ?_
  obtain rfl : ys = [] := hys
  rfl

/-- The interpretation of the witness: every operation is an idle kernel, the conversion is the
floor of a nonnegative real cell. -/
noncomputable def idleInterp (Op : Type) : Interp Op IdxTst ℝ where
  call _ d ins outs τ m := (BlockFn.mk 1 0 (fun _ => 0) (fun _ => []) (fun _ => [])
    fun _ _ _ => some []).apply d ins outs τ m
  test _ _ _ _ := none
  index _ a m := (m.readBlocks a (a.map fun _ => 1)).bind fun xs => toNatFn id xs.flatten

/-- **Witness**: the contract of an idle kernel and the contract of the conversion can be met
together, for every signature and every kernel. -/
theorem exists_isIdle_isToNat (o : Op) : ∃ (K : Type) (dec : K → ℝ) (J : Interp Op IdxTst K),
    J.Meets .total o ((idleRel (K := K)).spec AnyOperands) ∧ IsToNat dec J := by
  have hfn : (idleInterp Op).IsFn .total o (BlockFn.mk 1 0 (fun _ => 0) (fun _ => [])
      (fun _ => []) fun _ _ _ => some []) AnyOperands :=
    Interp.ofFns_isFn (Tst := IdxTst) (fun _ : Op => BlockFn.mk 1 0 (fun _ => 0) (fun _ => [])
      (fun _ => []) fun _ _ _ => some []) .total o AnyOperands
  refine ⟨ℝ, id, idleInterp Op, hfn.meets_rel (fun _ _ _ _ => trivial) rfl rfl (fun _ => rfl)
    (fun _ => rfl) (fun _ => rfl) fun _ _ _ _ _ _ _ _ _ _ _ => ⟨[], rfl, rfl, rfl⟩,
    fun a m xs h => ?_⟩
  change ((m.readBlocks a (a.map fun _ => 1)).bind fun xs => toNatFn id xs.flatten) = _
  rw [h]
  rfl

/-- **The exact counts of a split**, carried by the logic: one conversion, one call at the size
read and one at the rest. -/
theorem runsW_split {J : Interp Op IdxTst K} {o : Op} {dec : K → ℝ}
    (hK : J.Meets .total o ((idleRel (K := K)).spec AnyOperands)) (hidx : IsToNat dec J)
    (W : Op → List ℕ → ℕ) {τ : Tape K} {k : ℕ} {x : ℕ × ℕ} {m : Mem K} {w : K}
    (hx : m.store.get x.1 x.2 = some w) (h0 : 0 ≤ dec w) (hle : ⌊dec w⌋₊ ≤ k) :
    RunsW J W τ (split o) ⟨[k, x.2], [x.1]⟩ m (max (W o [⌊dec w⌋₊]) (W o [k - ⌊dec w⌋₊]))
      fun c m' => m' = m ∧ c = Count.test .toNat [] +
        (Count.one o [⌊dec w⌋₊] + Count.one o [k - ⌊dec w⌋₊]) := by
  refine (RunsFromW.bindIdx (st := St.init m) rfl rfl (hidx.index_eq hx h0) hle
    (RunsFromW.seq (RunsFromW.call rfl (wp_idle hK rfl)) fun st' c hc => ?_)).runsW
  obtain ⟨rfl, hm⟩ := hc
  refine (RunsFromW.call rfl (wp_idle hK (m := st'.mem) rfl)).mono le_rfl ?_
  rintro c' m' ⟨rfl, rfl⟩
  exact ⟨hm, rfl⟩

/-- The weight of the kernels: a call at the size `n` weighs `T n`; queries weigh nothing. -/
noncomputable def kernWeight (T : ℕ → ℕ) : Count Op IdxTst →+ ℕ :=
  Count.weight fun _ d => T (d.headD 0)

/-- **The weighted count of a split, for every superadditive weight**: at most `T k`. -/
theorem weight_split_le {T : ℕ → ℕ} (hT : ∀ a b, T a + T b ≤ T (a + b)) (o : Op) {k v : ℕ}
    (hv : v ≤ k) :
    kernWeight T (Count.test (Op := Op) IdxTst.toNat [] +
      (Count.one o [v] + Count.one o [k - v])) ≤ T k := by
  simp only [kernWeight, map_add, Count.weight_test, Count.weight_one, List.headD_cons, zero_add]
  have := hT v (k - v)
  rwa [Nat.add_sub_cancel' hv] at this

/-! ### The split as an implementation: a weighted accounting certificate -/

/-- The upper signature: a kernel `work [k] [x] []`, whose cell `x` holds the split. -/
inductive SOp where
  /-- The kernel. -/
  | work
  deriving DecidableEq

/-- The lower signature: a kernel `base [k] [] []`. -/
inductive LOp where
  /-- The kernel. -/
  | base
  deriving DecidableEq

/-- `work [k] [x] []` by a split over `base`. -/
def splitImpl : Impl LOp IdxTst := ⟨1, 1, 0, split .base⟩

/-- The table. -/
def splitTable : Table SOp LOp IdxTst := fun _ => .inl splitImpl

/-- **The weighted accounting certificate of the split**, for every superadditive weight `T`:
a run of the implementation of `work [k]` adds at most `T k` to the weight, whatever the split
it reads. No hypothesis on the lower interpretation. By the rules of the liberal counted
judgment (`NLAlib.Ops.RunsFromWL`): the index binder at the value read, two calls. -/
theorem splitTable_accountsW (I : Interp LOp IdxTst K) {T : ℕ → ℕ}
    (hT : ∀ a b, T a + T b ≤ T (a + b)) :
    splitTable.AccountsW I (fun _ _ => 0) (kernWeight T) (fun _ d => T (d.headD 0))
      (fun _ _ => 0) := by
  refine Table.AccountsW.of_runsFromWL (fun o R hR τ d a st hd ha => ?_) fun o o' h => by cases h
  cases hR
  obtain ⟨k, rfl⟩ := List.length_eq_one_iff.mp hd
  obtain ⟨x, rfl⟩ := List.length_eq_one_iff.mp ha
  refine RunsFromWL.bindIdx (B := k) rfl rfl fun v hv _ => ?_
  refine (RunsFromWL.seq (Q := fun c _ => c = Count.one LOp.base [v] + Count.one LOp.base [k - v])
    (RunsFromWL.call (d := [v]) rfl fun _ _ => trivial) fun st' c hc =>
    (RunsFromWL.call (d := [k - v]) rfl fun _ _ => trivial).mono le_rfl ?_).mono (by simp) ?_
  · exact fun c' _ hc' => hc.1 ▸ hc'.1 ▸ rfl
  · rintro c - rfl
    exact weight_split_le hT LOp.base hv

/-! ### An algorithm over the kernel, linked -/

/-- The contract of `work`: the cell holds a split of the size; nothing changes. -/
@[simps (attr := storeNF)]
def workRel (dec : K → ℝ) : BlockRel K where
  nd := 1
  inLens _ := [1]
  outLens _ := []
  dom d X _ := ∃ w, X = [[w]] ∧ 0 ≤ dec w ∧ ⌊dec w⌋₊ ≤ d.headD 0
  rel _ _ _ ys := ys = []

/-- The split meets the contract of `work`, over an idle lower kernel and an exact
conversion. -/
theorem splitImpl_spec {I : Interp LOp IdxTst K} {dec : K → ℝ}
    (hK : I.Meets .total .base ((idleRel (K := K)).spec AnyOperands)) (hidx : IsToNat dec I) :
    splitImpl.Meets I .total ((workRel dec).spec AnyOperands) := by
  refine Impl.meets_rel fun d ins outs τ m X hnd _ hl hr hdom hz => ?_
  obtain ⟨k, rfl⟩ := List.length_eq_one_iff.mp hnd
  obtain ⟨w, rfl, h0, hle⟩ := hdom
  obtain ⟨x, hx, -⟩ : ∃ x, ins = [x] ∧ m.store.get x.1 x.2 = some w := by
    obtain ⟨x, xs, rfl, hx, e⟩ := Mem.readBlocks_one hr
    cases e
    exact ⟨x, rfl, by simpa using Store.get_of_readBlock hx Nat.zero_lt_one w⟩
  subst hx
  obtain rfl : outs = [] := by
    rcases outs with _ | ⟨z, outs⟩
    · rfl
    · exact hz.elim
  have hxw : m.store.get x.1 x.2 = some w := by
    obtain ⟨x', xs, e, hx, e'⟩ := Mem.readBlocks_one hr
    cases e
    cases e'
    simpa using Store.get_of_readBlock hx Nat.zero_lt_one w
  refine ⟨⟨rfl, rfl, rfl⟩, wp_bindIdx rfl rfl (hidx.index_eq hxw h0) hle
    (wp_seq ((wp_idle hK rfl).mono ?_))⟩
  rintro m' rfl
  exact (wp_idle hK rfl).mono fun m' e => ⟨[], rfl, rfl, by rw [e]; rfl⟩

/-- Two calls of `work` at the size `k`. Index variables: `k`, the offset of the cell. -/
def twice : Stmt SOp IdxTst :=
  .seq (.call .work [.var 0] [⟨0, .var 1⟩] []) (.call .work [.var 0] [⟨0, .var 1⟩] [])

/-- **The linked program, with a weighted count**: `twice` linked through the split runs, and
for every superadditive `T` the weight of its counts of `base` is at most `2 T k`, whatever the
split stored in the cell. The static count of the linked tree would charge every split. -/
theorem runsW_twice_link {I : Interp LOp IdxTst K} {dec : K → ℝ}
    (hK : I.Meets .total .base ((idleRel (K := K)).spec AnyOperands)) (hidx : IsToNat dec I)
    {T : ℕ → ℕ} (hT : ∀ a b, T a + T b ≤ T (a + b)) {τ : Tape K} {k : ℕ} {x : ℕ × ℕ}
    {m : Mem K} {w : K} (hx : m.store.get x.1 x.2 = some w) (h0 : 0 ≤ dec w)
    (hle : ⌊dec w⌋₊ ≤ k) :
    RunsW I (fun _ _ => 0) τ (twice.link splitTable) ⟨[k, x.2], [x.1]⟩ m 0
      fun c m' => kernWeight T c ≤ 2 * T k ∧ m' = m := by
  have hW : (I.link splitTable).Meets .total .work ((workRel dec).spec AnyOperands) :=
    Interp.link_meets rfl (splitImpl_spec hK hidx)
  have hcall : ∀ m₀ : Mem K, m₀ = m → Wp .total (I.link splitTable) τ
      (.call .work [.var 0] [⟨0, .var 1⟩] []) ⟨[k, x.2], [x.1]⟩ (· = m) m₀ := by
    rintro m₀ rfl
    refine wp_call_rel hW (d := [k]) (a := [x]) (b := []) rfl rfl rfl rfl rfl rfl trivial
      (by simp [Store.lt_length_of_get hx])
      (BlockFn.readBlocks_cells_one.mpr ⟨w, hx, rfl⟩) ⟨w, rfl, h0, hle⟩ trivial
      fun ys _ hys => ?_
    obtain rfl : ys = [] := hys
    rfl
  obtain ⟨m', hrun, rfl⟩ : Wp .total (I.link splitTable) τ twice ⟨[k, x.2], [x.1]⟩ (· = m) m :=
    wp_seq ((hcall m rfl).mono fun m' e => hcall m' e)
  have hruns := runs_iff_runsW.mp (Runs.of_run hrun rfl fun _ _ => 0)
  refine exec_link_weight (t := fun _ => 2 * T k) (splitTable_accountsW I hT)
    (hruns.mono (by simp [twice, staticPeak]) fun c m' ⟨hc, hm⟩ => ⟨?_, hm.symm⟩)
  refine (Count.lift_mono _ hc).trans (le_of_eq ?_)
  simp [twice, staticCost, useCost, Count.lift, Count.one, two_mul]

end NLAlib.Ops.Examples
