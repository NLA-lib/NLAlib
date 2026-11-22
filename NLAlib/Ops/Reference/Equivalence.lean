/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Reference.Accounting
public import NLAlib.Ops.Cert

/-!
# Equivalence of declarative and canonical execution

The reference rules are connected to the evaluator with exact outcomes, rather than an
upper bound on accounting or a conditional statement about a successful output.

## Main results

* `NLAlib.Ops.Reference.execution_iff_exec`: exact agreement on the entire execution outcome.
* `NLAlib.Ops.Reference.exec_eq_none_iff`: failure is the absence of a source derivation.
* `NLAlib.Ops.Program.certifies_iff_reference`: the mathematical meaning of a certificate.
* `NLAlib.Ops.Algorithm.reference_correct`: a certificate obeys the reference rules and bounds.
-/

@[expose] public section

namespace NLAlib.Ops.Reference

variable {Op Tst K : Type} (I : Interp Op Tst K) (R : ResourceModel Op Tst) (τ : Tape K)

private abbrev Agrees (s : Stmt Op Tst) : Prop :=
  ∀ (ρ : Env) (a b : State Op Tst K), a.cur ≤ a.peak →
    (Derives I R τ s ρ a b ↔ instrumented I R τ s ρ a = some b)

private theorem memory_of_instrumented {s : Stmt Op Tst} {ρ : Env} {a b : State Op Tst K}
    (h : instrumented I R τ s ρ a = some b) : eval I τ s ρ a.mem = some b.mem := by
  have hm := run_of_exec h
  rw [run_instrument] at hm
  exact hm

private theorem agrees_skip : Agrees I R τ .skip := by
  intro ρ a b ha
  rw [instrumented_skip I R τ ρ a ha]
  constructor
  · intro h
    cases h
    rfl
  · intro h
    cases h
    exact .skip ρ a

private theorem agrees_abort : Agrees I R τ .abort := by
  intro ρ a b _
  constructor
  · intro h
    exact (not_derives_abort h).elim
  · intro h
    cases h

private theorem agrees_seq (s t : Stmt Op Tst) (hs : Agrees I R τ s)
    (ht : Agrees I R τ t) : Agrees I R τ (.seq s t) := by
  intro ρ a b ha
  rw [instrumented_seq I R τ s t ρ a ha, Option.bind_eq_some_iff]
  constructor
  · intro h
    cases h with
    | seq h₁ h₂ =>
      have h₁' := (hs ρ (charge (core .sequence) a) _ ha).mp h₁
      exact ⟨_, h₁', (ht _ _ _ (consistent_of_evalCounted h₁' ha)).mp h₂⟩
  · rintro ⟨mid, h₁, h₂⟩
    exact .seq ((hs ρ (charge (core .sequence) a) _ ha).mpr h₁)
      ((ht _ _ _ (consistent_of_evalCounted h₁ ha)).mpr h₂)

private theorem agrees_call (o : Op) (ds : List IExp) (ins outs : List Operand) :
    Agrees I R τ (.call o ds ins outs) := by
  intro ρ a b ha
  constructor
  · intro h
    cases h with
    | call hd hx hy hl hr hshape =>
      rw [instrumented_call I R τ o ds ins outs ρ a ha hd hx hy]
      simp only [Interp.callS, if_pos hl, hr, Option.bind_some, if_pos hshape, Option.map_some]
  · intro h
    have hm := memory_of_instrumented I R τ h
    obtain ⟨d, hd, hm⟩ := Option.bind_eq_some_iff.mp hm
    obtain ⟨xs, hx, hm⟩ := Option.bind_eq_some_iff.mp hm
    obtain ⟨ys, hy, hm⟩ := Option.bind_eq_some_iff.mp hm
    have hl := Interp.live_of_callS hm
    have hshape := Interp.shape_of_callS hm
    rw [instrumented_call I R τ o ds ins outs ρ a ha hd hx hy, hm,
      Option.map_some] at h
    have hr : I.call o d xs ys τ a.mem = some b.mem := by
      rw [Interp.callS_of_live hl] at hm
      obtain ⟨m, hr, hm⟩ := Option.bind_eq_some_iff.mp hm
      split_ifs at hm
      cases hm
      exact hr
    have hc := Derives.call (I := I) (R := R) (τ := τ) hd hx hy hl hr hshape
    exact (Option.some.inj h) ▸ hc

private theorem agrees_ite (q : Tst) (ds : List IExp) (ins : List Operand)
    (s t : Stmt Op Tst) (hs : Agrees I R τ s) (ht : Agrees I R τ t) :
    Agrees I R τ (.ite q ds ins s t) := by
  intro ρ a b ha
  constructor
  · intro h
    cases h with
    | ite hd hx hq hb =>
      rw [instrumented_ite I R τ q ds ins s t ρ a ha hd hx hq]
      rename_i d xs v
      cases v <;> simp only [Bool.false_eq_true, ↓reduceIte] at hb ⊢
      · exact (ht ρ (charge (dimensions ds + operands ins + core .branch + Count.test q d) a)
          b ha).mp hb
      · exact (hs ρ (charge (dimensions ds + operands ins + core .branch + Count.test q d) a)
          b ha).mp hb
  · intro h
    have hm := memory_of_instrumented I R τ h
    obtain ⟨d, hd, hm⟩ := Option.bind_eq_some_iff.mp hm
    obtain ⟨xs, hx, hm⟩ := Option.bind_eq_some_iff.mp hm
    obtain ⟨v, hq, _⟩ := Option.bind_eq_some_iff.mp hm
    rw [instrumented_ite I R τ q ds ins s t ρ a ha hd hx hq] at h
    refine .ite hd hx hq ?_
    cases v <;> simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    · exact (ht ρ (charge (dimensions ds + operands ins + core .branch + Count.test q d) a)
        b ha).mpr h
    · exact (hs ρ (charge (dimensions ds + operands ins + core .branch + Count.test q d) a)
        b ha).mpr h

private theorem agrees_bindIdx (q : Tst) (ins : List Operand) (bound : IExp)
    (body : Stmt Op Tst) (ih : Agrees I R τ body) :
    Agrees I R τ (.bindIdx q ins bound body) := by
  intro ρ a b ha
  constructor
  · intro h
    cases h with
    | bindIdx hx hn hq hv hb =>
      rw [instrumented_bindIdx I R τ q ins bound body ρ a ha hx hn hq hv]
      exact (ih _ (charge _ a) b ha).mp hb
  · intro h
    have hm := memory_of_instrumented I R τ h
    obtain ⟨xs, hx, hm⟩ := Option.bind_eq_some_iff.mp hm
    obtain ⟨n, hn, hm⟩ := Option.bind_eq_some_iff.mp hm
    obtain ⟨v, hq, hm⟩ := Option.bind_eq_some_iff.mp hm
    split_ifs at hm with hv
    rw [instrumented_bindIdx I R τ q ins bound body ρ a ha hx hn hq hv] at h
    exact .bindIdx hx hn hq hv ((ih _ (charge _ a) b ha).mpr h)

private theorem agrees_frame (ds : List IExp) (args : List Operand) (body : Stmt Op Tst)
    (ih : Agrees I R τ body) : Agrees I R τ (.frame ds args body) := by
  intro ρ a b ha
  constructor
  · intro h
    cases h with
    | frame hd hx hl hb =>
      rw [instrumented_frame I R τ ds args body ρ a ha hd hx hl]
      exact (ih _ (charge _ a) b ha).mp hb
  · intro h
    have hm := memory_of_instrumented I R τ h
    obtain ⟨d, hd, hm⟩ := Option.bind_eq_some_iff.mp hm
    obtain ⟨xs, hx, hm⟩ := Option.bind_eq_some_iff.mp hm
    split_ifs at hm with hl
    rw [instrumented_frame I R τ ds args body ρ a ha hd hx hl] at h
    exact .frame hd hx hl ((ih _ (charge _ a) b ha).mpr h)

private theorem agrees_allocAs (fmt : StorageFormat) (len : IExp) (body : Stmt Op Tst)
    (ih : Agrees I R τ body) : Agrees I R τ (.allocAs fmt len body) := by
  intro ρ a b ha
  constructor
  · intro h
    cases h with
    | allocAs hn hb =>
      rename_i n mid
      rw [instrumented_allocAs I R τ fmt len body ρ a ha hn]
      have hstart : (allocated fmt n (charge (index len) a)).cur ≤
          (allocated fmt n (charge (index len) a)).peak := Nat.le_max_right _ _
      rw [(ih _ _ _ hstart).mp hb, Option.map_some]
  · intro h
    have hm := memory_of_instrumented I R τ h
    obtain ⟨n, hn, _⟩ := Option.bind_eq_some_iff.mp hm
    rw [instrumented_allocAs I R τ fmt len body ρ a ha hn] at h
    obtain ⟨mid, hb, rfl⟩ := Option.map_eq_some_iff.mp h
    exact .allocAs hn ((ih _ (allocated fmt n (charge (index len) a)) mid
      (Nat.le_max_right _ _)).mpr hb)

private theorem consistent_iter
    (f : ℕ → State Op Tst K → Option (State Op Tst K))
    (hf : ∀ i a b, f i a = some b → a.cur ≤ a.peak → b.cur ≤ b.peak)
    {n : ℕ} {a b : State Op Tst K} (h : iter f n a = some b)
    (ha : a.cur ≤ a.peak) : b.cur ≤ b.peak := by
  induction n generalizing b with
  | zero => cases h; exact ha
  | succ n ih =>
    obtain ⟨mid, hp, hb⟩ := Option.bind_eq_some_iff.mp h
    exact hf n mid b hb (ih hp)

private noncomputable abbrev roundBody (body : Stmt Op Tst) (ρ : Env) (i : ℕ) :=
  evalCounted I.instrument (instrumentWorkspace R.workspace) τ
    (.seq (tally [.round]) body.instrument) (ρ.pushIdx i)

private theorem repeats_iff (body : Stmt Op Tst) (ih : Agrees I R τ body) (ρ : Env)
    (n : ℕ) (a b : State Op Tst K) (ha : a.cur ≤ a.peak) :
    Repeats I R τ body ρ n a b ↔ iter (roundBody I R τ body ρ) n a = some b := by
  induction n generalizing b with
  | zero =>
    constructor
    · intro h; cases h; rfl
    · intro h; cases h; exact .zero body ρ a
  | succ n hp =>
    constructor
    · intro h
      cases h with
      | succ hpre hbody =>
        have hpre' := (hp _).mp hpre
        have hmid := consistent_iter _
          (fun _ _ _ h hc => consistent_of_evalCounted h hc) hpre' ha
        change (iter (roundBody I R τ body ρ) n a).bind _ = _
        rw [hpre', Option.bind_some]
        unfold roundBody
        rw [eval_after_tally I R τ _ _ _ _ hmid]
        simp only [charges_cons, charges_nil, add_zero]
        exact (ih _ (charge (core .round) _) _ hmid).mp hbody
    · intro h
      obtain ⟨mid, hpre, hbody⟩ := Option.bind_eq_some_iff.mp h
      have hmid := consistent_iter _
        (fun _ _ _ h hc => consistent_of_evalCounted h hc) hpre ha
      unfold roundBody at hbody
      rw [eval_after_tally I R τ _ _ _ _ hmid] at hbody
      simp only [charges_cons, charges_nil, add_zero] at hbody
      exact .succ ((hp _).mpr hpre) ((ih _ (charge (core .round) mid) b hmid).mpr hbody)

private theorem agrees_loop (n : IExp) (body : Stmt Op Tst) (ih : Agrees I R τ body) :
    Agrees I R τ (.loop n body) := by
  intro ρ a b ha
  constructor
  · intro h
    cases h with
    | loop hn hb =>
      rw [instrumented_loop I R τ n body ρ a ha hn]
      exact (repeats_iff I R τ body ih ρ _ (charge (index n + core .loop) a) b ha).mp hb
  · intro h
    have hm := memory_of_instrumented I R τ h
    obtain ⟨k, hn, _⟩ := Option.bind_eq_some_iff.mp hm
    rw [instrumented_loop I R τ n body ρ a ha hn] at h
    exact .loop hn ((repeats_iff I R τ body ih ρ k
      (charge (index n + core .loop) a) b ha).mpr h)

private noncomputable abbrev whileBody (ds : List IExp) (ins : List Operand)
    (body : Stmt Op Tst) (ρ : Env) (i : ℕ) :=
  evalCounted I.instrument (instrumentWorkspace R.workspace) τ
    (.seq (tally (indexBookkeeping ds ++ operandBookkeeping ins ++ [.round]))
      body.instrument) (ρ.pushIdx i)

private noncomputable abbrev whileRun (q : Tst) (ds : List IExp) (ins : List Operand)
    (body : Stmt Op Tst) (ρ : Env) :=
  whileIter (fun i => I.instrument.testSt q ds ins (ρ.pushIdx i))
    (whileBody I R τ ds ins body ρ)

private theorem while_false (q : Tst) (ds : List IExp) (ins : List Operand)
    (body : Stmt Op Tst) (ρ : Env) (n i : ℕ) (a : State Op Tst K)
    {d : List ℕ} {xs : List (ℕ × ℕ)}
    (hd : IExp.evalList (ρ.pushIdx i).idx ds = some d)
    (hx : Operand.evalList (ρ.pushIdx i) ins = some xs)
    (hq : I.test q d xs a.mem = some false) :
    whileRun I R τ q ds ins body ρ (n + 1) i a =
      some (i, charge (Count.test q d) a) := by
  simp only [whileRun, whileIter, Interp.testSt, hd, hx, Option.bind_some,
    Interp.instrument, hq, Option.map_some, Bool.false_eq_true, ↓reduceIte]
  rfl

private theorem while_true (q : Tst) (ds : List IExp) (ins : List Operand)
    (body : Stmt Op Tst) (ρ : Env) (n i : ℕ) (a : State Op Tst K) (ha : a.cur ≤ a.peak)
    {d : List ℕ} {xs : List (ℕ × ℕ)}
    (hd : IExp.evalList (ρ.pushIdx i).idx ds = some d)
    (hx : Operand.evalList (ρ.pushIdx i) ins = some xs)
    (hq : I.test q d xs a.mem = some true) :
    whileRun I R τ q ds ins body ρ (n + 1) i a =
      (instrumented I R τ body (ρ.pushIdx i)
        (charge (Count.test q d + dimensions ds + operands ins + core .round) a)).bind
          (whileRun I R τ q ds ins body ρ n (i + 1)) := by
  simp only [whileRun, whileIter, Interp.testSt, hd, hx, Option.bind_some,
    Interp.instrument, hq, Option.map_some, ↓reduceIte]
  unfold whileBody
  rw [eval_after_tally I R τ _ _ _ _ (show (a.tick q d).cur ≤ (a.tick q d).peak from ha)]
  simp only [charges_append, charges_dimensions, charges_operands, charges_cons,
    charges_nil, add_zero, charge, St.tick, add_assoc]

private theorem consistent_while (q : Tst) (ds : List IExp) (ins : List Operand)
    (body : Stmt Op Tst) (ρ : Env) {n i j : ℕ} {a b : State Op Tst K}
    (h : whileRun I R τ q ds ins body ρ n i a = some (j, b))
    (ha : a.cur ≤ a.peak) : b.cur ≤ b.peak := by
  have hh := whileIter_rel
    (R := fun a b : State Op Tst K => a.cur ≤ a.peak → b.cur ≤ b.peak)
    (fun _ hc => hc) (fun _ _ _ h₁ h₂ hc => h₂ (h₁ hc))
    (fun i a bs ht hc => by
      obtain ⟨d, _, _, he⟩ := Interp.testSt_eq_some ht
      rw [he]
      exact hc)
    (fun _ _ _ hb hc => consistent_of_evalCounted hb hc) h
  exact hh.1 ha

private theorem while_iff (q : Tst) (ds : List IExp) (ins : List Operand)
    (body : Stmt Op Tst) (ih : Agrees I R τ body) (ρ : Env) (n i : ℕ)
    (a : State Op Tst K) (j : ℕ) (b : State Op Tst K) (ha : a.cur ≤ a.peak) :
    While I R τ q ds ins body ρ n i a j b ↔
      whileRun I R τ q ds ins body ρ n i a = some (j, b) := by
  induction n generalizing i a j b with
  | zero =>
    constructor
    · intro h; cases h; rfl
    · intro h; cases h; exact .cap q ds ins body ρ i a
  | succ n hp =>
    constructor
    · intro h
      cases h with
      | stop hd hx hq => exact while_false I R τ q ds ins body ρ n i a hd hx hq
      | step hd hx hq hb ht =>
        rw [while_true I R τ q ds ins body ρ n i a ha hd hx hq]
        have hb' := (ih _ (charge _ a) _ ha).mp hb
        rw [hb', Option.bind_some]
        exact (hp _ _ _ _ (consistent_of_evalCounted hb' ha)).mp ht
    · intro h
      have htest : ∃ bs, I.instrument.testSt q ds ins (ρ.pushIdx i) a = some bs := by
        obtain ⟨bs, ht, _⟩ := Option.bind_eq_some_iff.mp h
        exact ⟨bs, ht⟩
      obtain ⟨bs, htest⟩ := htest
      obtain ⟨d, hd, htest⟩ := Option.bind_eq_some_iff.mp htest
      obtain ⟨xs, hx, htest⟩ := Option.bind_eq_some_iff.mp htest
      obtain ⟨v, hq, _⟩ := Option.map_eq_some_iff.mp htest
      cases v with
      | false =>
        rw [while_false I R τ q ds ins body ρ n i a hd hx hq] at h
        cases h
        exact .stop hd hx hq
      | true =>
        rw [while_true I R τ q ds ins body ρ n i a ha hd hx hq] at h
        obtain ⟨mid, hb, ht⟩ := Option.bind_eq_some_iff.mp h
        exact .step hd hx hq ((ih _ (charge _ a) mid ha).mpr hb)
          ((hp _ _ _ _ (consistent_of_evalCounted hb ha)).mpr ht)

private theorem agrees_whileFuel (fuel : IExp) (q : Tst) (ds : List IExp)
    (ins : List Operand) (body next : Stmt Op Tst) (hb : Agrees I R τ body)
    (hk : Agrees I R τ next) : Agrees I R τ (.whileFuel fuel q ds ins body next) := by
  intro ρ a b ha
  constructor
  · intro h
    cases h with
    | whileFuel hn hw hc =>
      rw [instrumented_whileFuel I R τ fuel q ds ins body next ρ a ha hn]
      have hw' := (while_iff I R τ q ds ins body hb ρ _ 0 (charge _ a) _ _ ha).mp hw
      dsimp only [whileRun, whileBody] at hw'
      rw [hw', Option.bind_some]
      have hmid := consistent_while I R τ q ds ins body ρ hw' ha
      rw [eval_after_tally I R τ _ _ _ _ hmid]
      simp only [charges_append, charges_dimensions, charges_operands, charges_cons,
        charges_nil, add_zero]
      exact (hk _ (charge _ _) _ hmid).mp hc
  · intro h
    have hm := memory_of_instrumented I R τ h
    obtain ⟨n, hn, _⟩ := Option.bind_eq_some_iff.mp hm
    rw [instrumented_whileFuel I R τ fuel q ds ins body next ρ a ha hn] at h
    obtain ⟨⟨j, mid⟩, hw, hc⟩ := Option.bind_eq_some_iff.mp h
    have hmid := consistent_while I R τ q ds ins body ρ hw ha
    rw [eval_after_tally I R τ _ _ _ _ hmid] at hc
    simp only [charges_append, charges_dimensions, charges_operands, charges_cons,
      charges_nil, add_zero] at hc
    exact .whileFuel hn
      ((while_iff I R τ q ds ins body hb ρ n 0 (charge _ a) j mid ha).mpr hw)
      ((hk _ (charge _ mid) b hmid).mpr hc)

private theorem agrees_all (s : Stmt Op Tst) : Agrees I R τ s := by
  induction s with
  | skip => exact agrees_skip I R τ
  | abort => exact agrees_abort I R τ
  | seq s t hs ht => exact agrees_seq I R τ s t hs ht
  | call o ds ins outs => exact agrees_call I R τ o ds ins outs
  | ite q ds ins s t hs ht => exact agrees_ite I R τ q ds ins s t hs ht
  | loop n body ih => exact agrees_loop I R τ n body ih
  | whileFuel fuel q ds ins body next hb hk =>
    exact agrees_whileFuel I R τ fuel q ds ins body next hb hk
  | bindIdx q ins bound body ih => exact agrees_bindIdx I R τ q ins bound body ih
  | allocAs fmt len body ih => exact agrees_allocAs I R τ fmt len body ih
  | frame ds args body ih => exact agrees_frame I R τ ds args body ih
  | note n s ih =>
    intro ρ a b ha
    rw [derives_note_iff]
    exact ih ρ a b ha

/-- Declarative source execution and the instrumented evaluator agree on every consistent
accounting state, including the exact count, tape position, current scratch and peak. -/
theorem derives_iff_instrumented (s : Stmt Op Tst) (ρ : Env) (a b : State Op Tst K)
    (ha : a.cur ≤ a.peak) :
    Derives I R τ s ρ a b ↔ instrumented I R τ s ρ a = some b :=
  agrees_all I R τ s ρ a b ha

/-- Canonical execution succeeds with exactly an outcome when the independent source rules
derive that same outcome. No admission, success or resource bound is a premise. -/
theorem execution_iff_exec {r b : ℕ} (p : Program Op Tst r b)
    (formats : Fin b → StorageFormat) (d : Fin r → ℕ) (m : Mem K)
    (out : State Op Tst K) :
    Execution p I R formats τ d m out ↔ exec p I R formats τ d m = some out := by
  unfold Execution exec
  by_cases ht : p.wellTyped R formats = true ∧ m.store.length = b
  · rw [if_pos ht]
    constructor
    · rintro ⟨_, _, raw, hd, hout⟩
      have hr := (derives_iff_instrumented I R τ p.body _ (St.init m) raw (by simp [St.init])).mp hd
      unfold instrumented at hr
      rw [hr, Option.map_some]
      exact congrArg some hout.symm
    · intro h
      obtain ⟨raw, hr, hout⟩ := Option.map_eq_some_iff.mp h
      exact ⟨ht.1, ht.2, raw,
        (derives_iff_instrumented I R τ p.body _ (St.init m) raw (by simp [St.init])).mpr hr,
        hout.symm⟩
  · rw [if_neg ht]
    constructor
    · rintro ⟨hf, hl, _⟩
      exact (ht ⟨hf, hl⟩).elim
    · intro h
      cases h

/-- Canonical execution fails exactly when the source rules have no successful derivation.
Thus success equivalence also accounts for every execution failure. -/
theorem exec_eq_none_iff {r b : ℕ} (p : Program Op Tst r b)
    (formats : Fin b → StorageFormat) (d : Fin r → ℕ) (m : Mem K) :
    exec p I R formats τ d m = none ↔ ¬ ∃ out, Execution p I R formats τ d m out := by
  constructor
  · rintro he ⟨out, hd⟩
    have h := (execution_iff_exec I R τ p formats d m out).mp hd
    rw [he] at h
    cases h
  · intro h
    cases he : exec p I R formats τ d m with
    | none => rfl
    | some out =>
      exact (h ⟨out, (execution_iff_exec I R τ p formats d m out).mpr he⟩).elim

/-- The reference rules determine the entire outcome uniquely, including all accounting. -/
theorem Execution.unique {r b : ℕ} {p : Program Op Tst r b}
    {formats : Fin b → StorageFormat} {d : Fin r → ℕ} {m : Mem K}
    {a b' : State Op Tst K} (ha : Execution p I R formats τ d m a)
    (hb : Execution p I R formats τ d m b') : a = b' := by
  have h₁ := (execution_iff_exec I R τ p formats d m a).mp ha
  have h₂ := (execution_iff_exec I R τ p formats d m b').mp hb
  exact Option.some.inj (h₁.symm.trans h₂)

end NLAlib.Ops.Reference

namespace NLAlib.Ops.Program

variable {Op Tst K : Type} {r b : ℕ} {P : Problem K r b}

/-- Certification is equivalent to total execution under the independent source rules,
with the same scratch, counts, work, span, resident memory and output on every admitted input. -/
theorem certifies_iff_reference (p : Program Op Tst r b) (M : AccessModel Op Tst P)
    (S : Specification Op Tst P) :
    p.Certifies M S ↔
      ∀ d, P.valid d → ∀ (x : P.Input d) (I : Interp Op Tst K), M.contracts d x I → ∀ τ,
        ∃ st, Reference.Execution p I M.resources P.formats τ d (P.initial d x) st ∧
          st.peak ≤ S.scratch d ∧ st.cost ≤ S.budget d ∧
          M.resources.work st.cost ≤ S.work d ∧ M.resources.span st.cost ≤ S.span d ∧
          P.initialBytes d x + st.peak ≤ S.memory d ∧ S.good d x τ st.cost st.mem := by
  constructor
  · intro h d hd x I hI τ
    obtain ⟨st, hr, hbounds⟩ := h d hd x I hI τ
    exact ⟨st, (Reference.execution_iff_exec I M.resources τ p P.formats d
      (P.initial d x) st).mpr hr, hbounds⟩
  · intro h d hd x I hI τ
    obtain ⟨st, hr, hbounds⟩ := h d hd x I hI τ
    exact ⟨st, (Reference.execution_iff_exec I M.resources τ p P.formats d
      (P.initial d x) st).mp hr, hbounds⟩

end NLAlib.Ops.Program

namespace NLAlib.Ops.Algorithm

variable {Op Tst K : Type} {r b : ℕ} {P : Problem K r b}
  {M : AccessModel Op Tst P} {S : Specification Op Tst P}

/-- A certificate has its advertised meaning under the independent source rules: every
admitted input, interpreter and tape has one execution obeying all five resource bounds
and the output condition on that same count and memory. -/
theorem reference_correct (A : Algorithm M S) (d : Fin r → ℕ) (hd : P.valid d)
    (x : P.Input d) (I : Interp Op Tst K) (hI : M.contracts d x I) (τ : Tape K) :
    ∃ st, Reference.Execution A.program I M.resources P.formats τ d (P.initial d x) st ∧
      st.peak ≤ S.scratch d ∧ st.cost ≤ S.budget d ∧
      M.resources.work st.cost ≤ S.work d ∧ M.resources.span st.cost ≤ S.span d ∧
      P.initialBytes d x + st.peak ≤ S.memory d ∧ S.good d x τ st.cost st.mem := by
  exact (A.program.certifies_iff_reference M S).mp A.correct d hd x I hI τ

end NLAlib.Ops.Algorithm
