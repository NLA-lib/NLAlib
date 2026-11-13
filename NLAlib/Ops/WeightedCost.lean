/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.CountedLoop
public import NLAlib.Ops.CallSupport
public import NLAlib.Ops.Certification

/-!
# Weighted bounds before combining alternative operation shapes

A bounded query can select different matrix dimensions on different executions. Summing
the weights of a pointwise count supremum charges all these shapes simultaneously. The
weighted bound below takes scalar maxima after weighting each alternative, while retaining
every actually executed query and every capped-loop round. It estimates resources of the
existing counted evaluator; it defines no new execution semantics.

## Main results

* `NLAlib.Ops.stmtWeightedCost`: scalar weighted resource bound for a statement tree.
* `NLAlib.Ops.evalCounted_weight_le`: the bound applies to actual counted instructions.
-/

@[expose] public section

namespace NLAlib.Ops

variable {Op Tst K : Type}

/-- Scalar weighted cost of the existing statement tree. Branches and bounded query answers
take the maximum of their weighted costs. A capped while loop reserves its possible tests
and bodies plus the largest continuation cost over the possible stopping rounds. -/
def stmtWeightedCost (op : Op → List ℕ → ℕ) (query : Tst → List ℕ → ℕ) :
    Stmt Op Tst → List ℕ → ℕ
  | .skip, _ | .abort, _ => 0
  | .seq s t, idx => stmtWeightedCost op query s idx + stmtWeightedCost op query t idx
  | .call o ds _ _, idx => ((IExp.evalList idx ds).map (op o)).getD 0
  | .ite q ds _ s t, idx => ((IExp.evalList idx ds).map (query q)).getD 0 +
      max (stmtWeightedCost op query s idx) (stmtWeightedCost op query t idx)
  | .whileFuel fuel q ds _ s k, idx =>
      ∑ i ∈ Finset.range ((fuel.eval idx).getD 0),
          (((IExp.evalList (idx ++ [i]) ds).map (query q)).getD 0 +
            stmtWeightedCost op query s (idx ++ [i])) +
        (Finset.range ((fuel.eval idx).getD 0 + 1)).sup fun j =>
          stmtWeightedCost op query k (idx ++ [j])
  | .bindIdx q _ bound s, idx => query q [] +
      (Finset.range ((bound.eval idx).getD 0 + 1)).sup fun v =>
        stmtWeightedCost op query s (idx ++ [v])
  | .allocAs _ _ s, idx => stmtWeightedCost op query s idx
  | .loop n s, idx => ∑ i ∈ Finset.range ((n.eval idx).getD 0),
      stmtWeightedCost op query s (idx ++ [i])
  | .frame ds args s, idx =>
      match IExp.evalList idx ds, IExp.evalList idx (args.map Operand.off) with
      | some d, some os => stmtWeightedCost op query s (d ++ os)
      | _, _ => 0

private theorem whileIter_weight_le
    {test : ℕ → St Op Tst K → Option (Bool × St Op Tst K)}
    {body : ℕ → St Op Tst K → Option (St Op Tst K)}
    {weight : Count Op Tst → ℕ} {ct cb : ℕ → ℕ}
    (ht : ∀ i a bs, test i a = some bs → weight bs.2.cost ≤ weight a.cost + ct i)
    (hb : ∀ i a b, body i a = some b → weight b.cost ≤ weight a.cost + cb i)
    {r i : ℕ} {a : St Op Tst K} {js : ℕ × St Op Tst K}
    (h : whileIter test body r i a = some js) :
    weight js.2.cost ≤ weight a.cost + ∑ l ∈ Finset.range r, (ct (i + l) + cb (i + l)) := by
  induction r generalizing i a with
  | zero => cases h; simp
  | succ r ih =>
    have hsum : ct i + cb i + ∑ l ∈ Finset.range r, (ct (i + 1 + l) + cb (i + 1 + l)) =
        ∑ l ∈ Finset.range (r + 1), (ct (i + l) + cb (i + l)) := by
      rw [Finset.sum_range_succ', add_comm]
      simp [Nat.add_assoc, Nat.add_comm 1]
    obtain ⟨bs, hbs, h⟩ := Option.bind_eq_some_iff.mp h
    have ht' := ht i a bs hbs
    split_ifs at h with hv
    · obtain ⟨b, hb', h⟩ := Option.bind_eq_some_iff.mp h
      have hb'' := hb i bs.2 b hb'
      have hi := ih h
      rw [← hsum]
      omega
    · cases h
      change weight bs.2.cost ≤ _
      rw [← hsum]
      omega

private theorem testSt_weight_le {I : Interp Op Tst K} {q : Tst} {ds : List IExp}
    {ins : List Operand} {ρ : Env} {a : St Op Tst K} {bs : Bool × St Op Tst K}
    (op : Op → List ℕ → ℕ) (query : Tst → List ℕ → ℕ)
    (h : I.testSt q ds ins ρ a = some bs) :
    Count.lift (Sum.elim op query) bs.2.cost ≤ Count.lift (Sum.elim op query) a.cost +
      ((IExp.evalList ρ.idx ds).map (query q)).getD 0 := by
  obtain ⟨d, hd, _, he⟩ := Interp.testSt_eq_some h
  rw [he]
  simp only [St.tick, map_add, Count.test, Count.lift_single, one_nsmul,
    Sum.elim_inr, hd, Option.map_some, Option.getD_some, le_refl]

private theorem whileFuel_weight_le {I : Interp Op Tst K} {W : Op → List ℕ → ℕ}
    {τ : Tape K} {s k : Stmt Op Tst} (op : Op → List ℕ → ℕ) (query : Tst → List ℕ → ℕ)
    (ihs : ∀ ρ a b, evalCounted I W τ s ρ a = some b →
      Count.lift (Sum.elim op query) b.cost ≤ Count.lift (Sum.elim op query) a.cost +
        stmtWeightedCost op query s ρ.idx)
    (ihk : ∀ ρ a b, evalCounted I W τ k ρ a = some b →
      Count.lift (Sum.elim op query) b.cost ≤ Count.lift (Sum.elim op query) a.cost +
        stmtWeightedCost op query k ρ.idx)
    {fuel : IExp} {q : Tst} {ds : List IExp} {ins : List Operand} {ρ : Env}
    {a b : St Op Tst K} (h : evalCounted I W τ (.whileFuel fuel q ds ins s k) ρ a = some b) :
    Count.lift (Sum.elim op query) b.cost ≤ Count.lift (Sum.elim op query) a.cost +
      stmtWeightedCost op query (.whileFuel fuel q ds ins s k) ρ.idx := by
  obtain ⟨n, hn, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨js, hj, h⟩ := Option.bind_eq_some_iff.mp h
  have hloop := whileIter_weight_le
    (ct := fun i => ((IExp.evalList (ρ.idx ++ [i]) ds).map (query q)).getD 0)
    (cb := fun i => stmtWeightedCost op query s (ρ.idx ++ [i]))
    (fun i a bs htest => testSt_weight_le op query htest)
    (fun i a b hbody => ihs (ρ.pushIdx i) a b hbody) hj
  have hindex := whileIter_rel (R := fun _ _ : St Op Tst K => True)
    (fun _ => trivial) (fun _ _ _ _ _ => trivial) (fun _ _ _ _ => trivial)
    (fun _ _ _ _ => trivial) hj
  have hcont := ihk _ _ _ h
  have hs : stmtWeightedCost op query k (ρ.idx ++ [js.1]) ≤
      (Finset.range (n + 1)).sup fun j => stmtWeightedCost op query k (ρ.idx ++ [j]) :=
    Finset.le_sup (s := Finset.range (n + 1)) (b := js.1)
      (f := fun j => stmtWeightedCost op query k (ρ.idx ++ [j]))
      (Finset.mem_range.mpr (by omega))
  simp only [stmtWeightedCost, hn, Option.getD_some]
  simp only [Nat.zero_add] at hloop
  exact hcont.trans (by
    simpa only [Nat.add_assoc, Env.idx_pushIdx] using Nat.add_le_add hloop hs)

/-- Actual weighted instruction counts obey the scalar estimate, including every query.
The hypothesis is an auxiliary resource analysis of the existing counted execution; it
does not supply termination. Total program logic supplies termination independently. -/
theorem evalCounted_weight_le (op : Op → List ℕ → ℕ) (query : Tst → List ℕ → ℕ)
    {I : Interp Op Tst K} {W : Op → List ℕ → ℕ} {τ : Tape K}
    {s : Stmt Op Tst} {ρ : Env} {a b : St Op Tst K}
    (h : evalCounted I W τ s ρ a = some b) :
    Count.lift (Sum.elim op query) b.cost ≤ Count.lift (Sum.elim op query) a.cost +
      stmtWeightedCost op query s ρ.idx := by
  induction s generalizing ρ a b with
  | skip => cases h; simp [stmtWeightedCost]
  | abort => cases h
  | seq s t ihs iht =>
    obtain ⟨a₁, ha₁, hb⟩ := Option.bind_eq_some_iff.mp h
    exact (iht hb).trans (by
      simpa only [stmtWeightedCost, Nat.add_assoc] using
        Nat.add_le_add_right (ihs ha₁) (stmtWeightedCost op query t ρ.idx))
  | call o ds ins outs =>
    obtain ⟨d, hd, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨xs, hxs, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨ys, hys, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨m', hm, rfl⟩ := Option.map_eq_some_iff.mp h
    simp only [map_add, Count.one, Count.lift_single, one_nsmul, Sum.elim_inl,
      stmtWeightedCost, hd, Option.map_some, Option.getD_some, le_refl]
  | ite q ds ins s t ihs iht =>
    obtain ⟨d, hd, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨xs, hxs, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨v, hv, h⟩ := Option.bind_eq_some_iff.mp h
    have ht : Count.lift (Sum.elim op query) (a.tick q d).cost =
        Count.lift (Sum.elim op query) a.cost + query q d := by
      simp only [St.tick, map_add, Count.test, Count.lift_single, one_nsmul, Sum.elim_inr]
    simp only [stmtWeightedCost, hd, Option.map_some, Option.getD_some]
    cases v
    · have hb := iht h
      rw [ht] at hb
      exact hb.trans (by omega)
    · have hb := ihs h
      rw [ht] at hb
      exact hb.trans (by omega)
  | whileFuel fuel q ds ins s k ihs ihk =>
    exact whileFuel_weight_le op query (fun _ _ _ h => ihs h) (fun _ _ _ h => ihk h) h
  | bindIdx q ins bound s ih =>
    obtain ⟨xs, hxs, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨B, hB, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨v, hv, h⟩ := Option.bind_eq_some_iff.mp h
    split_ifs at h with hvB
    have hb := ih h
    simp only [St.tick, map_add, Count.test, Count.lift_single, one_nsmul,
      Sum.elim_inr, Env.pushIdx] at hb
    have hs : stmtWeightedCost op query s (ρ.idx ++ [v]) ≤
        (Finset.range (B + 1)).sup fun j => stmtWeightedCost op query s (ρ.idx ++ [j]) :=
      Finset.le_sup (s := Finset.range (B + 1)) (b := v)
        (f := fun j => stmtWeightedCost op query s (ρ.idx ++ [j]))
        (Finset.mem_range.mpr (by omega))
    simp only [stmtWeightedCost, hB, Option.getD_some]
    omega
  | allocAs fmt len s ih =>
    obtain ⟨n, hn, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨a₁, ha₁, rfl⟩ := Option.map_eq_some_iff.mp h
    have hb := ih ha₁
    simpa only [stmtWeightedCost, Env.idx_pushBuf] using hb
  | loop n s ih =>
    obtain ⟨k, hk, h⟩ := Option.bind_eq_some_iff.mp h
    have hb := (iter_weight_le_of_invariant (P := fun _ _ => True)
      (w := fun i => stmtWeightedCost op query s (ρ.idx ++ [i]))
      (fun i a b _ hi => ⟨trivial, ih hi⟩) trivial h).2
    simpa only [stmtWeightedCost, hk, Option.getD_some] using hb
  | frame ds args s ih =>
    obtain ⟨d, hd, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨xs, hxs, h⟩ := Option.bind_eq_some_iff.mp h
    split_ifs at h with hl
    simpa only [stmtWeightedCost, hd, Operand.evalList_off_of_evalList hxs,
      Env.idx_frame] using ih h

/-- A frame's scalar weighted bound follows from the evaluated dimensions and a body bound
uniform in its operand offsets. Failed operand evaluation contributes zero weighted cost. -/
theorem stmtWeightedCost_frame_le (op : Op → List ℕ → ℕ) (query : Tst → List ℕ → ℕ)
    {ds : List IExp} {args : List Operand} {s : Stmt Op Tst} {idx d : List ℕ} {b : ℕ}
    (hd : IExp.evalList idx ds = some d)
    (h : ∀ os, stmtWeightedCost op query s (d ++ os) ≤ b) :
    stmtWeightedCost op query (.frame ds args s) idx ≤ b := by
  simp only [stmtWeightedCost, hd]
  cases IExp.evalList idx (args.map Operand.off) with
  | none => exact Nat.zero_le _
  | some os => exact h os

/-- A frame also fixes the offset-list length, including when a body locates a newly bound
index after its dimensions and operands. -/
theorem stmtWeightedCost_frame_le_of_length
    (op : Op → List ℕ → ℕ) (query : Tst → List ℕ → ℕ)
    {ds : List IExp} {args : List Operand} {s : Stmt Op Tst} {idx d : List ℕ} {b : ℕ}
    (hd : IExp.evalList idx ds = some d)
    (h : ∀ os, os.length = args.length → stmtWeightedCost op query s (d ++ os) ≤ b) :
    stmtWeightedCost op query (.frame ds args s) idx ≤ b := by
  simp only [stmtWeightedCost, hd]
  cases he : IExp.evalList idx (args.map Operand.off) with
  | none => exact Nat.zero_le _
  | some os => exact h os (by simpa only [List.length_map] using IExp.length_of_evalList he)

/-- A zero-test guard executes its body at most once, so a uniform bound for the body is
also a bound for the guarded statement. Invalid condition evaluation contributes zero. -/
theorem stmtWeightedCost_ifZero_le (op : Op → List ℕ → ℕ) (query : Tst → List ℕ → ℕ)
    {e : IExp} {s : Stmt Op Tst} {idx : List ℕ} {b : ℕ}
    (h : ∀ i, stmtWeightedCost op query s (idx ++ [i]) ≤ b) :
    stmtWeightedCost op query (.ifZero e s) idx ≤ b := by
  let n := ((IExp.const 1 - e).eval idx).getD 0
  have hn : n ≤ 1 := by
    dsimp [n]
    cases he : e.eval idx <;> simp [IExp.eval, he]
  change (∑ i ∈ Finset.range n, stmtWeightedCost op query s (idx ++ [i])) ≤ b
  calc
    _ ≤ ∑ _i ∈ Finset.range n, b := Finset.sum_le_sum fun i _ => h i
    _ = n * b := by simp
    _ ≤ b := by simpa only [one_mul] using Nat.mul_le_mul_right b hn

private theorem option_map_zero {α : Type} (x : Option α) :
    (x.map (fun _ => (0 : ℕ))).getD 0 = 0 := by cases x <;> rfl

/-- If a syntactic operation check permits only zero-weight operations, the statement's
weighted cost is zero at every index environment when query weights are also zero. -/
theorem stmtWeightedCost_zero_of_allOps (op : Op → List ℕ → ℕ) (p : Op → Bool)
    (hp : ∀ o, p o = true → ∀ ds, op o ds = 0) (s : Stmt Op Tst)
    (hs : s.allOps p = true) (idx : List ℕ) :
    stmtWeightedCost op (fun _ _ => 0) s idx = 0 := by
  have hsup (t : Finset ℕ) : (t.sup fun _ => (0 : ℕ)) = 0 := Finset.sup_bot t
  induction s generalizing idx with
  | skip | abort => rfl
  | call o ds ins outs =>
    simp only [stmtWeightedCost]
    cases IExp.evalList idx ds with
    | none => rfl
    | some d => exact hp o hs d
  | seq s t ihs iht =>
    obtain ⟨hs, ht⟩ := Bool.and_eq_true_iff.mp hs
    simp only [stmtWeightedCost, ihs hs, iht ht, Nat.zero_add]
  | ite q ds ins s t ihs iht =>
    obtain ⟨hs, ht⟩ := Bool.and_eq_true_iff.mp hs
    simp only [stmtWeightedCost, ihs hs, iht ht, option_map_zero, max_self, Nat.zero_add]
  | whileFuel fuel q ds ins s k ihs ihk =>
    obtain ⟨hs, hk⟩ := Bool.and_eq_true_iff.mp hs
    simp only [stmtWeightedCost, ihs hs, ihk hk, option_map_zero, Nat.zero_add,
      Finset.sum_const_zero, hsup]
  | bindIdx q ins bound s ih => simp only [stmtWeightedCost, ih hs, hsup, Nat.zero_add]
  | allocAs fmt len s ih => exact ih hs idx
  | loop n s ih => simp only [stmtWeightedCost, ih hs, Finset.sum_const_zero]
  | frame ds args s ih =>
    simp only [stmtWeightedCost]
    cases IExp.evalList idx ds <;> cases IExp.evalList idx (args.map Operand.off) <;>
      simp only [ih hs]

/-- Total word-level logic and a scalar weighted source bound give a total instrumented
execution with that bound on its exact original-count projection. Structural instructions
remain in the actual count. Stored/primitive scratch has its independent source peak bound. -/
theorem Wp.runs_original_weighted {I : Interp Op Tst K} {τ : Tape K}
    {s : Stmt Op Tst} {ρ : Env} {m : Mem K} {Q : Mem K → Prop}
    (h : Wp .total I τ s ρ Q m) (op : Op → List ℕ → ℕ) (query : Tst → List ℕ → ℕ)
    (W : Op → List ℕ → ℕ) {b : ℕ} (hb : stmtWeightedCost op query s ρ.idx ≤ b) :
    ConditionalRunsW I.instrument (instrumentWorkspace W) τ s.instrument ρ m
      (stmtPeak W s ρ.idx) (fun c m' =>
        Count.lift (Sum.elim op query) (Count.original c) ≤ b ∧ Q m') := by
  obtain ⟨m', hr, hQ⟩ := h
  have hi : eval I.instrument τ s.instrument ρ m = some m' := by
    rw [run_instrument]
    exact hr
  obtain ⟨st, he, _, hp, hQ⟩ := ConditionalRuns.of_run hi hQ (instrumentWorkspace W)
  obtain ⟨raw, hraw, _, hc⟩ := evalCounted_original_instrument he
  have hw := evalCounted_weight_le op query hraw
  simp only [St.init, map_zero, Nat.zero_add] at hw
  refine ⟨st, he, ?_, ?_, hQ⟩
  · simpa only [stmtPeak_instrument] using hp
  · rw [← hc]
    exact hw.trans hb

end NLAlib.Ops
