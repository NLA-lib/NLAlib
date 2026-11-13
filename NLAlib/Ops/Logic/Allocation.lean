/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Logic.BlockSequence
public import Mathlib.Data.List.GetD

/-!
# Scoped scratch allocations and surviving outputs

A program body proved on allocated scratch returns its ordinary output block. The shared rule
discharges scratch removal and transports that block to the caller's final store, so algorithm
proofs never unfold pop operations or reconstruct an output after each allocation scope.
The allocation tactic extracts the actual allocation chain and proves equality of statement
trees before applying the rules, preserving every explicit storage format.

## Main results

* `NLAlib.Ops.writes_allocs_readBlock`: an exact output block survives a whole scratch chain.
* `NLAlib.Ops.writes_allocs_readBlocks`: a tuple of outputs survives the same scratch cleanup.
* `NLAlib.Ops.Stmt.splitAllocations`: the actual allocation prefix and remaining subtree.
* `NLAlib.Ops.evalCounted_allocsAs_inv`: its inner run, fresh geometry and preserved counts.
* `allocs_preserving`: allocation sizes, postcondition preservation and ordinary body goals.
-/

@[expose] public section

namespace NLAlib.Ops

variable {K Op Tst : Type} {md : Mode} {I : Interp Op Tst K} {τ : Tape K}
  {ρ : Env} {m : Mem K}

/-- A block in a fresh scratch handle is included in the caller's declared footprint joined
with its scratch region. Allocation clients do not unfold footprint membership themselves. -/
theorem Fp.inBlock_le_sup_above {F : Fp} {L b off n : ℕ} (hb : L ≤ b) :
    Store.inBlock b off n ≤ F ⊔ Fp.above L := by
  rintro b' i ⟨rfl, _, _⟩
  exact Or.inr hb

/-- Blocks in surviving handles are disjoint from every fresh scratch handle. -/
theorem Fp.blocks_disj_above {L : ℕ} {zs : List (ℕ × ℕ)} {ls : List ℕ}
    (hz : ∀ z ∈ zs, z.1 < L) : Fp.Disj (Fp.blocks zs ls) (Fp.above L) := by
  induction zs generalizing ls with
  | nil => exact Fp.disj_bot_left _
  | cons z zs ih =>
    cases ls with
    | nil => exact Fp.disj_bot_left _
    | cons l ls =>
      refine Fp.disj_sup_left.mpr ⟨?_, ih (fun z hz' => hz z (by simp [hz']))⟩
      intro b i hb ha
      have h := hz z (by simp)
      obtain ⟨rfl, _, _⟩ := hb
      exact Nat.not_le_of_gt h ha

/-- Agreement below a handle preserves all output-capacity obligations in those handles.
This transports a whole operand tuple across scratch allocation or removal at once. -/
theorem Mem.room_eq_of_below {L : ℕ} {μ μ' : Mem K} {zs : List (ℕ × ℕ)} {ls : List ℕ}
    (h : Store.Below L μ.store μ'.store) (hz : ∀ z ∈ zs, z.1 < L) :
    μ'.Room zs ls = μ.Room zs ls := by
  induction zs generalizing ls with
  | nil => cases ls <;> rfl
  | cons z zs ih =>
    cases ls with
    | nil => rfl
    | cons l ls =>
      simp only [Mem.Room, (h z.1 (hz z (by simp))).1,
        ih (fun z hz' => hz z (by simp [hz']))]

/-- A block collection whose handles are all fresh lies wholly in fresh scratch. -/
theorem Fp.blocks_le_above {L : ℕ} {zs : List (ℕ × ℕ)} {ls : List ℕ}
    (hz : ∀ z ∈ zs, L ≤ z.1) : Fp.blocks zs ls ≤ Fp.above L := by
  induction zs generalizing ls with
  | nil => exact bot_le
  | cons z zs ih =>
    cases ls with
    | nil => exact bot_le
    | cons l ls =>
      refine sup_le ?_ (ih (fun z hz' => hz z (by simp [hz'])))
      intro b i hb
      obtain ⟨rfl, _, _⟩ := hb
      exact hz z (by simp)

/-- The operand tuple of an allocation chain is apart, independently of buffer capacities.
Every scratch handle occurs exactly once. -/
theorem Fp.apart_allocs (L : ℕ) (ns : List ℕ) :
    Fp.Apart ((List.range ns.length).map fun i => (L + i, 0)) ns := by
  have hget (i : ℕ) (hi : i < ns.length) :
      ((List.range ns.length).map fun j => (L + j, 0)).getD i (0, 0) = (L + i, 0) := by
    rw [List.getD_eq_getElem _ _ (by simpa using hi)]
    simp only [List.getElem_map, List.getElem_range]
  apply Fp.Apart.of_disj_getD
  intro i hi j hj hne
  have hi' : i < ns.length := by simpa only [List.length_map, List.length_range, min_self] using hi
  have hj' : j < ns.length := by simpa only [List.length_map, List.length_range, min_self] using hj
  rw [hget i hi', hget j hj']
  exact Fp.disj_inBlock_of_ne (by simpa using hne)

/-- Fresh buffers with the allocation chain's declared lengths have room for the whole
scratch operand tuple. No per-buffer capacity proof is required by the caller. -/
theorem Mem.room_allocs (μ : Mem K) (L : ℕ) (ns : List ℕ)
    (hlens : ∀ i (hi : i < ns.length), μ.store.len (L + i) = ns[i]) :
    μ.Room ((List.range ns.length).map fun i => (L + i, 0)) ns := by
  induction ns generalizing L with
  | nil => trivial
  | cons n ns ih =>
    have hz := hlens 0 (by simp)
    change μ.store.len (L + 0) = n at hz
    simp only [Nat.add_zero] at hz
    have ht := ih (L + 1) (fun i hi => by
      have hx := hlens (i + 1) (by simpa using hi)
      change μ.store.len (L + (i + 1)) = ns[i] at hx
      simpa only [Nat.add_assoc, Nat.add_comm 1 i] using hx)
    simpa only [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map,
      Function.comp_def, Nat.succ_eq_add_one, Nat.add_zero, Nat.add_assoc, Nat.add_comm 1,
      Mem.room_cons, Mem.room_nil, Nat.zero_add, hz, le_refl, true_and] using ht

/-- Every handle introduced by an allocation chain is live in the extended store. -/
theorem Mem.live_allocs (μ : Mem K) (L : ℕ) (ns : List ℕ)
    (hlen : μ.store.length = L + ns.length) :
    μ.Live ((List.range ns.length).map fun i => (L + i, 0)) := by
  rintro z hz
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hz
  change L + i < μ.store.length
  rw [hlen]
  exact Nat.add_lt_add_left (List.mem_range.mp hi) L

/-- Split the leading scoped allocations from a statement. The remaining body is the actual
subtree, including its frame; formats and size expressions are retained verbatim. -/
def Stmt.splitAllocations : Stmt Op Tst → List (StorageFormat × IExp) × Stmt Op Tst
  | .allocAs format len body =>
      let rest := body.splitAllocations
      ((format, len) :: rest.1, rest.2)
  | body => ([], body)

/-- Reassembling the extracted allocation prefix returns the original statement exactly. -/
theorem Stmt.allocsAs_splitAllocations (s : Stmt Op Tst) :
    Stmt.allocsAs s.splitAllocations.1 s.splitAllocations.2 = s := by
  induction s with
  | allocAs format len body ih => exact congrArg (Stmt.allocAs format len) ih
  | _ => rfl

/-- A successful formatted allocation chain exposes its actual inner counted run and fresh
store geometry. Allocation and cleanup preserve counts. No relation between the inner and
outer scratch peaks is asserted by this decomposition. -/
theorem evalCounted_allocsAs_inv {W : Op → List ℕ → ℕ}
    {allocations : List (StorageFormat × IExp)} {body : Stmt Op Tst}
    {ns : List ℕ} {a b : St Op Tst K}
    (hn : IExp.evalList ρ.idx (allocations.map Prod.snd) = some ns)
    (hr : evalCounted I W τ (Stmt.allocsAs allocations body) ρ a = some b) :
    ∃ inner final : St Op Tst K,
      evalCounted I W τ body
        ⟨ρ.idx, ρ.buf ++ (List.range ns.length).map (a.mem.store.length + ·)⟩ inner =
          some final ∧
      inner.mem.store.length = a.mem.store.length + ns.length ∧
      (∀ i (hi : i < ns.length), inner.mem.store.len (a.mem.store.length + i) = ns[i]) ∧
      Store.Below a.mem.store.length a.mem.store inner.mem.store ∧
      inner.mem.pos = a.mem.pos ∧ inner.cost = a.cost ∧ final.cost = b.cost := by
  induction allocations generalizing ρ ns a b with
  | nil =>
    simp only [List.map_nil, IExp.evalList_nil, Option.some.injEq] at hn
    subst hn
    refine ⟨a, b, ?_, by simp, ?_, Store.Below.refl _ _, rfl, rfl, rfl⟩
    · simpa only [Stmt.allocsAs, List.length_nil, List.range_zero, List.map_nil,
        List.append_nil] using hr
    · intro i hi
      simp at hi
  | cons allocation allocations ih =>
    rw [List.map_cons, IExp.evalList_cons] at hn
    obtain ⟨n, hl, hn⟩ := Option.bind_eq_some_iff.mp hn
    obtain ⟨ns', hns', rfl⟩ := Option.map_eq_some_iff.mp hn
    simp only [Stmt.allocsAs, evalCounted, hl, Option.bind_some] at hr
    obtain ⟨last, hlast, rfl⟩ := Option.map_eq_some_iff.mp hr
    obtain ⟨inner, final, hbody, hlength, hlens, hBelow, hpos, hcost, hfinal⟩ :=
      ih (by simpa only [Env.idx_pushBuf] using hns') hlast
    dsimp only at hlength hlens hBelow hpos hcost hfinal
    have hlen : (a.mem.store.push n).length = a.mem.store.length + 1 := by simp
    have he : (⟨ρ.idx, ρ.buf ++
        (List.range (n :: ns').length).map (a.mem.store.length + ·)⟩ : Env) =
        ⟨(ρ.pushBuf a.mem.store.length).idx,
          (ρ.pushBuf a.mem.store.length).buf ++
            (List.range ns'.length).map ((a.mem.store.push n).length + ·)⟩ := by
      simp only [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map,
        Env.idx_pushBuf, Env.buf_pushBuf, hlen, List.append_assoc, List.singleton_append,
        Nat.add_zero]
      congr 3
      refine List.map_congr_left fun i _ => ?_
      simp only [Function.comp_apply]
      omega
    rw [← he] at hbody
    refine ⟨inner, final, hbody, by simp [hlength, hlen]; omega, ?_,
      (Store.below_push _ _).trans (hBelow.mono (by simp)), hpos, hcost, hfinal⟩
    intro i hi
    cases i with
    | zero =>
      simpa using (hBelow a.mem.store.length (by simp)).1.trans (by simp)
    | succ i =>
      have h := hlens i (by simpa using hi)
      simpa [hlen, Nat.add_assoc, Nat.add_comm 1 i] using h

/-- Scoped scratch can be removed once the postcondition depends only on surviving storage.
The body proves its ordinary postcondition; a single transport under agreement below the
caller's original handle count accounts for every allocation's cleanup. -/
theorem writes_allocsAs_preserving_post {allocations : List (StorageFormat × IExp)}
    {body : Stmt Op Tst} {ns : List ℕ} {F : Fp} {P : Mem K → Prop}
    (hn : IExp.evalList ρ.idx (allocations.map Prod.snd) = some ns)
    (hkeep : ∀ {s s' : Store K} {p : ℕ}, Store.Below m.store.length s s' →
      P ⟨s, p⟩ → P ⟨s', p⟩)
    (h : ∀ s₁ : Store K, s₁.length = m.store.length + ns.length →
      (∀ i (hi : i < ns.length), s₁.len (m.store.length + i) = ns[i]) →
      Store.Below m.store.length m.store s₁ →
      Writes md I τ body ⟨ρ.idx, ρ.buf ++ (List.range ns.length).map (m.store.length + ·)⟩
        (F ⊔ Fp.above m.store.length) P ⟨s₁, m.pos⟩) :
    Writes md I τ (Stmt.allocsAs allocations body) ρ F P m := by
  refine writes_allocsAs hn fun s₁ hs₁ hlens hBelow => ?_
  exact (h s₁ hs₁ hlens hBelow).mono le_rfl fun _ _ hp _ _ hBelow₂ => hkeep hBelow₂ hp

/-- Scoped cell scratch can be removed once the postcondition depends only on surviving
storage. This is the one-cell-format form of `writes_allocsAs_preserving_post`. -/
theorem writes_allocs_preserving_post {lens : List IExp} {body : Stmt Op Tst} {ns : List ℕ}
    {F : Fp} {P : Mem K → Prop} (hn : IExp.evalList ρ.idx lens = some ns)
    (hkeep : ∀ {s s' : Store K} {p : ℕ}, Store.Below m.store.length s s' →
      P ⟨s, p⟩ → P ⟨s', p⟩)
    (h : ∀ s₁ : Store K, s₁.length = m.store.length + ns.length →
      (∀ i (hi : i < ns.length), s₁.len (m.store.length + i) = ns[i]) →
      Store.Below m.store.length m.store s₁ →
      Writes md I τ body ⟨ρ.idx, ρ.buf ++ (List.range ns.length).map (m.store.length + ·)⟩
        (F ⊔ Fp.above m.store.length) P ⟨s₁, m.pos⟩) :
    Writes md I τ (Stmt.allocs lens body) ρ F P m := by
  refine writes_allocs hn fun s₁ hs₁ hlens hBelow => ?_
  exact (h s₁ hs₁ hlens hBelow).mono le_rfl fun _ _ hp _ _ hBelow₂ => hkeep hBelow₂ hp

/-- A scratch-allocation chain returns its declared output block at the specified final
tape position. Sampling may advance that position; scoped cleanup preserves it. -/
theorem writes_allocs_readBlock_at {lens : List IExp} {body : Stmt Op Tst} {ns : List ℕ}
    {z : ℕ × ℕ} {n pos : ℕ} {ys : List K}
    (hn : IExp.evalList ρ.idx lens = some ns) (hz : z.1 < m.store.length)
    (h : ∀ s₁ : Store K, s₁.length = m.store.length + ns.length →
      (∀ i (hi : i < ns.length), s₁.len (m.store.length + i) = ns[i]) →
      Store.Below m.store.length m.store s₁ →
      Writes md I τ body ⟨ρ.idx, ρ.buf ++ (List.range ns.length).map (m.store.length + ·)⟩
        (Store.inBlock z.1 z.2 n ⊔ Fp.above m.store.length)
        (fun m' => m'.pos = pos ∧ m'.store.readBlock z.1 z.2 n = some ys) ⟨s₁, m.pos⟩) :
    Writes md I τ (Stmt.allocs lens body) ρ (Store.inBlock z.1 z.2 n)
      (fun m' => m'.pos = pos ∧ m'.store.readBlock z.1 z.2 n = some ys) m := by
  exact writes_allocs_preserving_post hn
    (fun hBelow hp => ⟨hp.1, (hBelow.readBlock hz z.2 n).trans hp.2⟩) h

/-- A scratch-allocation chain preserves its declared output block and tape position. The
body may write its scratch buffers and the output region; no scratch content is an assumption
at entry, and every scratch allocation is removed before returning. -/
theorem writes_allocs_readBlock {lens : List IExp} {body : Stmt Op Tst} {ns : List ℕ}
    {z : ℕ × ℕ} {n : ℕ} {ys : List K}
    (hn : IExp.evalList ρ.idx lens = some ns) (hz : z.1 < m.store.length)
    (h : ∀ s₁ : Store K, s₁.length = m.store.length + ns.length →
      (∀ i (hi : i < ns.length), s₁.len (m.store.length + i) = ns[i]) →
      Store.Below m.store.length m.store s₁ →
      Writes md I τ body ⟨ρ.idx, ρ.buf ++ (List.range ns.length).map (m.store.length + ·)⟩
        (Store.inBlock z.1 z.2 n ⊔ Fp.above m.store.length)
        (fun m' => m'.pos = m.pos ∧ m'.store.readBlock z.1 z.2 n = some ys) ⟨s₁, m.pos⟩) :
    Writes md I τ (Stmt.allocs lens body) ρ (Store.inBlock z.1 z.2 n)
      (fun m' => m'.pos = m.pos ∧ m'.store.readBlock z.1 z.2 n = some ys) m := by
  exact writes_allocs_readBlock_at hn hz h

/-- Agreement below a handle preserves a tuple of block reads in existing buffers. -/
theorem Mem.readBlocks_eq_of_below {L : ℕ} {m m' : Mem K} {zs : List (ℕ × ℕ)}
    {ls : List ℕ} (h : Store.Below L m.store m'.store)
    (hz : ∀ z ∈ zs, z.1 < L) : m'.readBlocks zs ls = m.readBlocks zs ls := by
  induction zs generalizing ls with
  | nil => cases ls <;> rfl
  | cons z zs ih =>
    cases ls with
    | nil => rfl
    | cons l ls =>
      simp only [Mem.readBlocks, h.readBlock (hz z (by simp)) z.2 l,
        ih (fun z hz' => hz z (by simp [hz']))]

/-- A scratch-allocation chain returns a whole tuple of actual output blocks, preserving
position and releasing every scratch buffer. Output handles belong to the caller; the body
may modify only the declared output regions and fresh scratch. -/
theorem writes_allocs_readBlocks {lens : List IExp} {body : Stmt Op Tst} {ns : List ℕ}
    {zs : List (ℕ × ℕ)} {ls : List ℕ} {ys : List (List K)}
    (hn : IExp.evalList ρ.idx lens = some ns) (hz : m.Live zs)
    (h : ∀ s₁ : Store K, s₁.length = m.store.length + ns.length →
      (∀ i (hi : i < ns.length), s₁.len (m.store.length + i) = ns[i]) →
      Store.Below m.store.length m.store s₁ →
      Writes md I τ body ⟨ρ.idx, ρ.buf ++ (List.range ns.length).map (m.store.length + ·)⟩
        (Fp.blocks zs ls ⊔ Fp.above m.store.length)
        (fun m' => m'.pos = m.pos ∧ m'.readBlocks zs ls = some ys) ⟨s₁, m.pos⟩) :
    Writes md I τ (Stmt.allocs lens body) ρ (Fp.blocks zs ls)
      (fun m' => m'.pos = m.pos ∧ m'.readBlocks zs ls = some ys) m := by
  exact writes_allocs_preserving_post hn
    (fun hBelow hp => ⟨hp.1, (Mem.readBlocks_eq_of_below hBelow hz).trans hp.2⟩) h

open Lean Meta Elab Tactic in
/-- `allocs_preserving sizes` extracts every leading allocation from the actual `Writes`
statement. It leaves `sizes` for their evaluated lengths, `keep` for postcondition transport
under agreement below the caller's handles, and `body` for the ordinary body on fresh storage.
All explicit storage formats are retained. No execution assumption is introduced. -/
elab (name := tacticAllocsPreserving) "allocs_preserving " sizes:term : tactic => withMainContext do
  let goal ← getMainGoal
  let target := (← instantiateMVars (← goal.getType)).consumeMData
  unless target.isAppOf ``Writes do
    throwError "allocs_preserving: expected a Writes goal"
  let cleanGoal ← goal.change target
  replaceMainGoal [cleanGoal]
  let args := target.getAppArgs
  let original := args[args.size - 5]!
  let mut body := original
  let mut allocations : Array Expr := #[]
  repeat
    let stmt ← whnfD body
    let (``Stmt.allocAs, #[_, _, format, len, rest]) := stmt.getAppFnArgs | break
    allocations := allocations.push (← mkAppM ``Prod.mk #[format, len])
    body := rest
  if allocations.isEmpty then
    throwError "allocs_preserving: expected a leading allocation"
  let allocationType ← mkAppM ``Prod #[mkConst ``StorageFormat, mkConst ``IExp]
  let allocationList ← mkListLit allocationType allocations.toList
  let shell ← mkAppM ``Stmt.allocsAs #[allocationList, body]
  let originalTerm ← Term.exprToSyntax original
  let shellTerm ← Term.exprToSyntax shell
  let statementType ← Term.exprToSyntax (← inferType original)
  let shape ← mkIdent <$> getUnusedUserName `allocation_shell
  evalTactic (← `(tactic| have $shape : ($originalTerm : $statementType) = $shellTerm := by rfl))
  let rule ← `(Parser.Tactic.rwRule| $shape:term)
  evalTactic (← `(tactic| rw [$rule]))
  let allocationTerm ← Term.exprToSyntax allocationList
  let bodyTerm ← Term.exprToSyntax body
  evalTactic (← `(tactic| refine writes_allocsAs_preserving_post
    (allocations := $allocationTerm) (body := $bodyTerm) (ns := $sizes)
    ?sizes ?keep ?body))

end NLAlib.Ops
