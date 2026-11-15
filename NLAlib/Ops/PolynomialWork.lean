/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.ContextWork
public import NLAlib.Ops.WeightEnvelope
public import Mathlib.Tactic.Ring

/-!
# Context-sensitive polynomial bounds for complete program work

Each index slot retains its own polynomial exponent through frames and loops. Sequential
composition adds fixed coefficients and takes the larger degree. This separates the computed
polynomial loop degree from the number of scalar and structural instructions in the code.
Applying the estimate to instrumented syntax retains every canonical charge.

## Main results

* `NLAlib.Ops.stmtWeightedCost_le_coefficient_mul_pow`: full finite-envelope work majorant.
-/

@[expose] public section

namespace NLAlib.Ops

variable {Op Tst : Type}

private theorem power_mono {b i j : ℕ} (hb : 2 ≤ b) (h : i ≤ j) : b ^ i ≤ b ^ j :=
  pow_le_pow_right' (by omega) h

private theorem weighted_mono {b i j c w : ℕ} (hb : 2 ≤ b) (h : i ≤ j) :
    c * b ^ i * w ≤ c * b ^ j * w :=
  Nat.mul_le_mul_right w (Nat.mul_le_mul_left c (power_mono hb h))

private theorem values_push {b v e : ℕ} {idx degrees : List ℕ}
    (h : List.Forall₂ (fun x d => x ≤ b ^ d) idx degrees) (hv : v ≤ b ^ e) :
    List.Forall₂ (fun x d => x ≤ b ^ d) (idx ++ [v]) (degrees ++ [e]) :=
  List.rel_append h (.cons hv .nil)

private theorem eval_weight_le {α : Type} {f : α → List ℕ → ℕ}
    {b a e w : ℕ} {idx degrees : List ℕ} {ds : List IExp}
    (hb : 2 ≤ b) (hi : List.Forall₂ (fun v d => v ≤ b ^ d) idx degrees)
    (hd : IExp.listDegreeAt degrees ds ≤ e) (ha : ds.length ≤ a)
    (hw : ∀ o vs, vs.length ≤ a → (∀ x ∈ vs, x ≤ b ^ e) → f o vs ≤ w) (o : α) :
    ((IExp.evalList idx ds).map (f o)).getD 0 ≤ w := by
  cases hv : IExp.evalList idx ds with
  | none => exact Nat.zero_le _
  | some vs =>
    apply hw o vs
    · rw [IExp.length_of_evalList hv]
      exact ha
    · intro x hx
      exact (IExp.evalList_le_pow_listDegreeAt hb hi hv x hx).trans (power_mono hb hd)

private abbrev PolynomialWorkBound (op : Op → List ℕ → ℕ)
    (query : Tst → List ℕ → ℕ) (s : Stmt Op Tst) : Prop :=
  ∀ (b : ℕ) (idx degrees : List ℕ) (w : ℕ), 2 ≤ b →
    List.Forall₂ (fun v d => v ≤ b ^ d) idx degrees →
    WorkEnvelope op query s.callArity (b ^ s.callDegreeAt degrees) w →
    stmtWeightedCost op query s idx ≤ s.workCoefficient * b ^ s.workDegreeAt degrees * w

private theorem polynomial_seq (op : Op → List ℕ → ℕ) (query : Tst → List ℕ → ℕ)
    (s t : Stmt Op Tst) (hs : PolynomialWorkBound op query s)
    (ht : PolynomialWorkBound op query t) : PolynomialWorkBound op query (.seq s t) := by
  intro b idx degrees w hb hi hw
  have hS := hs b idx degrees w hb hi (hw.mono (Nat.le_max_left ..)
    (power_mono hb (Nat.le_max_left ..)))
  have hT := ht b idx degrees w hb hi (hw.mono (Nat.le_max_right ..)
    (power_mono hb (Nat.le_max_right ..)))
  change _ + _ ≤ _
  calc
    _ ≤ s.workCoefficient * b ^ max (s.workDegreeAt degrees) (t.workDegreeAt degrees) * w +
        t.workCoefficient * b ^ max (s.workDegreeAt degrees) (t.workDegreeAt degrees) * w :=
      Nat.add_le_add (hS.trans (weighted_mono hb (Nat.le_max_left ..)))
        (hT.trans (weighted_mono hb (Nat.le_max_right ..)))
    _ = _ := by simp only [Stmt.workCoefficient, Stmt.workDegreeAt]; ring

private theorem polynomial_loop (op : Op → List ℕ → ℕ) (query : Tst → List ℕ → ℕ)
    (n : IExp) (s : Stmt Op Tst) (hs : PolynomialWorkBound op query s) :
    PolynomialWorkBound op query (.loop n s) := by
  intro b idx degrees w hb hi hw
  have hdim : (n.eval idx).getD 0 ≤ b ^ n.degreeAt degrees := by
    cases hn : n.eval idx with
    | none => exact Nat.zero_le _
    | some v => exact n.eval_le_pow_degreeAt hb hi hn
  have hc : ∀ i ∈ Finset.range ((n.eval idx).getD 0),
      stmtWeightedCost op query s (idx ++ [i]) ≤
        s.workCoefficient * b ^ s.workDegreeAt (degrees ++ [n.degreeAt degrees]) * w := by
    intro i hi'
    exact hs _ _ _ _ hb (values_push hi
      ((Nat.le_of_lt (Finset.mem_range.mp hi')).trans hdim)) hw
  change (∑ i ∈ Finset.range _, _) ≤ _
  calc
    _ ≤ ∑ _i ∈ Finset.range ((n.eval idx).getD 0),
        s.workCoefficient * b ^ s.workDegreeAt (degrees ++ [n.degreeAt degrees]) * w :=
      Finset.sum_le_sum hc
    _ = (n.eval idx).getD 0 *
        (s.workCoefficient * b ^ s.workDegreeAt (degrees ++ [n.degreeAt degrees]) * w) := by simp
    _ ≤ b ^ n.degreeAt degrees *
        (s.workCoefficient * b ^ s.workDegreeAt (degrees ++ [n.degreeAt degrees]) * w) :=
      Nat.mul_le_mul_right _ hdim
    _ = _ := by simp only [Stmt.workCoefficient, Stmt.workDegreeAt, pow_add]; ring

private theorem polynomial_frame (op : Op → List ℕ → ℕ) (query : Tst → List ℕ → ℕ)
    (ds : List IExp) (args : List Operand) (s : Stmt Op Tst)
    (hs : PolynomialWorkBound op query s) : PolynomialWorkBound op query (.frame ds args s) := by
  intro b idx degrees w hb hi hw
  simp only [stmtWeightedCost]
  cases hd : IExp.evalList idx ds <;> cases ho : IExp.evalList idx (args.map Operand.off)
  all_goals try exact Nat.zero_le _
  rename_i d os
  apply hs _ _ _ _ hb ?_ hw
  simpa only [List.map_map, Function.comp_def] using
    List.rel_append (IExp.evalList_le_pow_degreeAt hb hi hd)
      (IExp.evalList_le_pow_degreeAt hb hi ho)

private theorem polynomial_ite (op : Op → List ℕ → ℕ) (query : Tst → List ℕ → ℕ)
    (q : Tst) (ds : List IExp) (args : List Operand) (s t : Stmt Op Tst)
    (hs : PolynomialWorkBound op query s) (ht : PolynomialWorkBound op query t) :
    PolynomialWorkBound op query (.ite q ds args s t) := by
  intro b idx degrees w hb hi hw
  have hST := polynomial_seq op query s t hs ht b idx degrees w hb hi
    (hw.mono (Nat.le_max_right ..) (power_mono hb (Nat.le_max_right ..)))
  have hQ : ((IExp.evalList idx ds).map (query q)).getD 0 ≤ w :=
    eval_weight_le hb hi (Nat.le_max_left ..) (Nat.le_max_left ..) hw.2 q
  have hu : w ≤ b ^ max (s.workDegreeAt degrees) (t.workDegreeAt degrees) * w :=
    Nat.le_mul_of_pos_left w (pow_pos (by omega) _)
  change _ + max _ _ ≤ _
  calc
    _ ≤ w + (stmtWeightedCost op query s idx + stmtWeightedCost op query t idx) :=
      Nat.add_le_add hQ (by omega)
    _ ≤ b ^ max (s.workDegreeAt degrees) (t.workDegreeAt degrees) * w +
        (s.workCoefficient + t.workCoefficient) *
          b ^ max (s.workDegreeAt degrees) (t.workDegreeAt degrees) * w :=
      Nat.add_le_add hu hST
    _ = _ := by simp only [Stmt.workCoefficient, Stmt.workDegreeAt]; ring

private theorem polynomial_bindIdx (op : Op → List ℕ → ℕ) (query : Tst → List ℕ → ℕ)
    (q : Tst) (args : List Operand) (bound : IExp) (s : Stmt Op Tst)
    (hs : PolynomialWorkBound op query s) :
    PolynomialWorkBound op query (.bindIdx q args bound s) := by
  intro b idx degrees w hb hi hw
  have hdim : (bound.eval idx).getD 0 ≤ b ^ bound.degreeAt degrees := by
    cases hn : bound.eval idx with
    | none => exact Nat.zero_le _
    | some v => exact bound.eval_le_pow_degreeAt hb hi hn
  have hsup : (Finset.range ((bound.eval idx).getD 0 + 1)).sup
      (fun i => stmtWeightedCost op query s (idx ++ [i])) ≤
      s.workCoefficient * b ^ s.workDegreeAt (degrees ++ [bound.degreeAt degrees]) * w := by
    apply Finset.sup_le
    intro i hi'
    apply hs _ _ _ _ hb (values_push hi ?_) hw
    exact (show i ≤ (bound.eval idx).getD 0 by
      have := Finset.mem_range.mp hi'; omega).trans hdim
  have hq : query q [] ≤ w := hw.2 q [] (by simp) (by simp)
  have hu : w ≤ b ^ s.workDegreeAt (degrees ++ [bound.degreeAt degrees]) * w :=
    Nat.le_mul_of_pos_left w (pow_pos (by omega) _)
  change _ + _ ≤ _
  calc
    _ ≤ b ^ s.workDegreeAt (degrees ++ [bound.degreeAt degrees]) * w +
        s.workCoefficient * b ^ s.workDegreeAt (degrees ++ [bound.degreeAt degrees]) * w :=
      Nat.add_le_add (hq.trans hu) hsup
    _ = _ := by simp only [Stmt.workCoefficient, Stmt.workDegreeAt]; ring

private theorem polynomial_while (op : Op → List ℕ → ℕ) (query : Tst → List ℕ → ℕ)
    (fuel : IExp) (q : Tst) (ds : List IExp) (args : List Operand) (s t : Stmt Op Tst)
    (hs : PolynomialWorkBound op query s) (ht : PolynomialWorkBound op query t) :
    PolynomialWorkBound op query (.whileFuel fuel q ds args s t) := by
  intro b idx degrees w hb hi hw
  let extended := degrees ++ [fuel.degreeAt degrees]
  have hdim : (fuel.eval idx).getD 0 ≤ b ^ fuel.degreeAt degrees := by
    cases hn : fuel.eval idx with
    | none => exact Nat.zero_le _
    | some v => exact fuel.eval_le_pow_degreeAt hb hi hn
  have hpush : ∀ i ≤ (fuel.eval idx).getD 0,
      List.Forall₂ (fun v d => v ≤ b ^ d) (idx ++ [i]) extended :=
    fun _ hi' => values_push hi (hi'.trans hdim)
  have hBody : ∀ i ≤ (fuel.eval idx).getD 0, stmtWeightedCost op query s (idx ++ [i]) ≤
      s.workCoefficient * b ^ s.workDegreeAt extended * w := by
    intro i hi'
    exact hs _ _ _ _ hb (hpush i hi') (hw.mono
      (by dsimp only [Stmt.callArity]; omega)
      (power_mono hb (by dsimp only [Stmt.callDegreeAt, extended]; omega)))
  have hCont : (Finset.range ((fuel.eval idx).getD 0 + 1)).sup
      (fun i => stmtWeightedCost op query t (idx ++ [i])) ≤
      t.workCoefficient * b ^ t.workDegreeAt extended * w := by
    apply Finset.sup_le
    intro i hi'
    exact ht _ _ _ _ hb (hpush i (by have := Finset.mem_range.mp hi'; omega)) (hw.mono
      (by dsimp only [Stmt.callArity]; omega)
      (power_mono hb (by dsimp only [Stmt.callDegreeAt, extended]; omega)))
  have hQuery : ∀ i ≤ (fuel.eval idx).getD 0,
      ((IExp.evalList (idx ++ [i]) ds).map (query q)).getD 0 ≤ w := by
    intro i hi'
    exact eval_weight_le hb (hpush i hi') (Nat.le_max_left ..) (Nat.le_max_left ..) hw.2 q
  have hu : w ≤ b ^ s.workDegreeAt extended * w :=
    Nat.le_mul_of_pos_left w (pow_pos (by omega) _)
  have hsum : (∑ i ∈ Finset.range ((fuel.eval idx).getD 0),
      (((IExp.evalList (idx ++ [i]) ds).map (query q)).getD 0 +
        stmtWeightedCost op query s (idx ++ [i]))) ≤
      (1 + s.workCoefficient) * b ^ (fuel.degreeAt degrees + s.workDegreeAt extended) * w := by
    calc
      _ ≤ ∑ _i ∈ Finset.range ((fuel.eval idx).getD 0),
          (b ^ s.workDegreeAt extended * w +
            s.workCoefficient * b ^ s.workDegreeAt extended * w) := by
        apply Finset.sum_le_sum
        intro i hi'
        have hi'' : i ≤ (fuel.eval idx).getD 0 := by
          have := Finset.mem_range.mp hi'; omega
        exact Nat.add_le_add ((hQuery i hi'').trans hu) (hBody i hi'')
      _ = (fuel.eval idx).getD 0 * (b ^ s.workDegreeAt extended * w +
          s.workCoefficient * b ^ s.workDegreeAt extended * w) := by simp
      _ ≤ b ^ fuel.degreeAt degrees * (b ^ s.workDegreeAt extended * w +
          s.workCoefficient * b ^ s.workDegreeAt extended * w) := Nat.mul_le_mul_right _ hdim
      _ = _ := by rw [pow_add]; ring
  change _ + _ ≤ _
  apply (Nat.add_le_add hsum hCont).trans
  calc
    _ ≤ (1 + s.workCoefficient) *
        b ^ max (fuel.degreeAt degrees + s.workDegreeAt extended) (t.workDegreeAt extended) * w +
        t.workCoefficient *
        b ^ max (fuel.degreeAt degrees + s.workDegreeAt extended) (t.workDegreeAt extended) * w :=
      Nat.add_le_add (weighted_mono hb (Nat.le_max_left ..))
        (weighted_mono hb (Nat.le_max_right ..))
    _ = _ := by simp only [Stmt.workCoefficient, Stmt.workDegreeAt]; dsimp [extended]; ring

/-- A complete weighted-work estimate with a structural coefficient, a slot-sensitive work
degree and a separate finite primitive dimension envelope. Applied to instrumented syntax,
this counts every original operation, query and structural instruction. -/
theorem stmtWeightedCost_le_coefficient_mul_pow
    (op : Op → List ℕ → ℕ) (query : Tst → List ℕ → ℕ)
    (s : Stmt Op Tst) {b : ℕ} (hb : 2 ≤ b) {idx degrees : List ℕ}
    (hi : List.Forall₂ (fun v d => v ≤ b ^ d) idx degrees) {w : ℕ}
    (hw : WorkEnvelope op query s.callArity (b ^ s.callDegreeAt degrees) w) :
    stmtWeightedCost op query s idx ≤ s.workCoefficient * b ^ s.workDegreeAt degrees * w := by
  have h : PolynomialWorkBound op query s := by
    clear hb hi hw b idx degrees w
    induction s with
    | skip | abort => intro b idx degrees w hb hi hw; exact Nat.zero_le _
    | seq s t hs ht => exact polynomial_seq op query s t hs ht
    | call o ds ins outs =>
      intro b idx degrees w hb hi hw
      simpa only [stmtWeightedCost, Stmt.workCoefficient, Stmt.workDegreeAt,
        pow_zero, mul_one, one_mul] using
        eval_weight_le hb hi le_rfl le_rfl hw.1 o
    | ite q ds args s t hs ht => exact polynomial_ite op query q ds args s t hs ht
    | whileFuel fuel q ds args s t hs ht =>
      exact polynomial_while op query fuel q ds args s t hs ht
    | bindIdx q args bound s hs => exact polynomial_bindIdx op query q args bound s hs
    | allocAs fmt len s hs => exact hs
    | loop n s hs => exact polynomial_loop op query n s hs
    | frame ds args s hs => exact polynomial_frame op query ds args s hs
  exact h b idx degrees w hb hi hw

/-- Canonical counted execution obeys the context-sensitive majorant for the full instrumented
tree. Query reservation preserves counts, so every declared work charge is included. -/
theorem Program.exec_work_le_coefficient_mul_pow {K : Type} {r buffers : ℕ}
    (p : Program Op Tst r buffers) (R : ResourceModel Op Tst)
    {I : Interp Op Tst K} {τ : Tape K} {formats : Fin buffers → StorageFormat}
    {d : Fin r → ℕ} {m : Mem K} {st : St (Op ⊕ Bookkeeping) Tst K}
    {base weight : ℕ} {degrees : List ℕ} (hb : 2 ≤ base)
    (hi : List.Forall₂ (fun v e => v ≤ base ^ e)
      (Program.environment (b := buffers) d).idx degrees)
    (hw : WorkEnvelope (Sum.elim R.operationWork R.coreWork) R.queryWork
      p.body.instrument.callArity (base ^ p.body.instrument.callDegreeAt degrees) weight)
    (hr : exec p I R formats τ d m = some st) :
    R.work st.cost ≤ p.body.instrument.workCoefficient *
      base ^ p.body.instrument.workDegreeAt degrees * weight := by
  unfold exec at hr
  split_ifs at hr with ht
  obtain ⟨raw, hraw, rfl⟩ := Option.map_eq_some_iff.mp hr
  have hcost := evalCounted_weight_le (Sum.elim R.operationWork R.coreWork) R.queryWork hraw
  have hmajor := stmtWeightedCost_le_coefficient_mul_pow
    (Sum.elim R.operationWork R.coreWork) R.queryWork p.body.instrument hb hi hw
  simp only [St.init, map_zero, Nat.zero_add] at hcost
  simpa only [St.reserveQueries, ResourceModel.work] using hcost.trans hmajor

end NLAlib.Ops
