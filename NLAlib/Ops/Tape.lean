/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Link
public import NLAlib.Ops.Contract

/-!
# Tapes

The tape of draws is an argument of the evaluator, so an interpretation, and the interpretation
induced by a table, is fixed before the sample. What a meaning may read of the tape is a clause
of the access model, not of a contract:

* `NLAlib.Ops.Interp.TapeLocal I o k`: at the memory `m` the meaning of `o` at the dimensions `d`
  depends on the tape only through the `k d` entries from the position `m.pos`, and advances the
  position by `k d`. `k = 0` is tape independence.
* `NLAlib.Ops.run_follows`: under tape-local operations a run depends on the tape only through the
  entries between its first and last positions.
* `NLAlib.Ops.run_pos_of_straight`: a tree without tests and index binders advances the position
  by its static window `NLAlib.Ops.staticWindow`.
* `NLAlib.Ops.Interp.TapeLocal.link` (**the window lemma**): the meaning induced by such an
  implementation is tape-local, with the window obtained by adding the windows of its calls.
* `NLAlib.Ops.Interp.ofFns_tapeLocal`: block functions are tape-local with their window.
-/

@[expose] public section

namespace NLAlib.Ops

variable {Op Op₁ Op₂ K : Type}

/-- **Tape locality** of the operation `o` with the window `k`. -/
def Interp.TapeLocal (I : Interp Op K) (o : Op) (k : List ℕ → ℕ) : Prop :=
  ∀ d ins outs m (τ τ' : ℕ → K), (∀ j < k d, τ (m.pos + j) = τ' (m.pos + j)) →
    I.call o d ins outs τ m = I.call o d ins outs τ' m ∧
      ∀ m', I.call o d ins outs τ m = some m' → m'.pos = m.pos + k d

/-- `f'`, a step under the tape `τ'`, follows `f`, the step under `τ`: a successful `f` does not
move the position back, and `f'` gives the same result if the tapes agree between the two
positions. -/
def Follows (τ τ' : ℕ → K) (f f' : Mem K → Option (Mem K)) : Prop :=
  ∀ a b, f a = some b →
    a.pos ≤ b.pos ∧ ((∀ j, a.pos ≤ j → j < b.pos → τ j = τ' j) → f' a = some b)

namespace Follows

variable {τ τ' : ℕ → K}

theorem bind {f f' g g' : Mem K → Option (Mem K)} (hf : Follows τ τ' f f')
    (hg : Follows τ τ' g g') :
    Follows τ τ' (fun a => (f a).bind g) (fun a => (f' a).bind g') := by
  intro a b h
  obtain ⟨c, hc, hb⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨h1, h2⟩ := hf a c hc
  obtain ⟨h3, h4⟩ := hg c b hb
  refine ⟨h1.trans h3, fun hag => ?_⟩
  simp only [h2 fun j hj hj' => hag j hj (hj'.trans_le h3), Option.bind_some]
  exact h4 fun j hj hj' => hag j (h1.trans hj) hj'

theorem iter {f f' : ℕ → Mem K → Option (Mem K)} (h : ∀ i, Follows τ τ' (f i) (f' i)) (k : ℕ) :
    Follows τ τ' (iter f k) (iter f' k) := by
  induction k with
  | zero =>
    intro a b hab
    cases hab
    exact ⟨le_rfl, fun _ => rfl⟩
  | succ k ih => exact ih.bind (h k)

theorem whileIter (test : Mem K → Option Bool) {body body' : Mem K → Option (Mem K)}
    (h : Follows τ τ' body body') (k : ℕ) :
    Follows τ τ' (whileIter test id body k) (whileIter test id body' k) := by
  induction k with
  | zero =>
    intro a b hab
    obtain ⟨c, hc, hb⟩ := Option.bind_eq_some_iff.mp hab
    cases c with
    | true => simp at hb
    | false =>
      simp only [Bool.false_eq_true, if_false, id, Option.some.injEq] at hb
      subst hb
      exact ⟨le_rfl, fun _ => by simp [NLAlib.Ops.whileIter, hc]⟩
  | succ k ih =>
    intro a b hab
    obtain ⟨c, hc, hb⟩ := Option.bind_eq_some_iff.mp hab
    cases c with
    | false =>
      simp only [Bool.false_eq_true, if_false, id, Option.some.injEq] at hb
      subst hb
      exact ⟨le_rfl, fun _ => by simp [NLAlib.Ops.whileIter, hc]⟩
    | true =>
      simp only [if_true, id] at hb
      obtain ⟨h1, h2⟩ := (h.bind ih) a b hb
      exact ⟨h1, fun hag => by simpa [NLAlib.Ops.whileIter, hc] using h2 hag⟩

end Follows

/-- The call of the evaluator under a tape-local operation. -/
theorem Interp.TapeLocal.callS {I : Interp Op K} {o : Op} {k : List ℕ → ℕ}
    (h : I.TapeLocal o k) (d : List ℕ) (ins outs : List (ℕ × ℕ)) (τ τ' : ℕ → K) :
    Follows τ τ' (I.callS o d ins outs τ) (I.callS o d ins outs τ') := by
  intro a b hab
  obtain ⟨m₁, h₁, hb⟩ := Option.bind_eq_some_iff.mp hab
  split_ifs at hb with hs
  simp only [Option.some.injEq] at hb
  subst hb
  have hpos := (h d ins outs a τ τ fun _ _ => rfl).2 m₁ h₁
  refine ⟨by omega, fun hag => ?_⟩
  have he := (h d ins outs a τ τ' fun j hj => hag _ (by omega) (by omega)).1
  rw [Interp.callS, ← he, h₁]
  simp [hs]

/-- **Under tape-local operations, a run depends on the tape only through the entries between its
first and last positions.** -/
theorem run_follows {I : Interp Op K} {k : Op → List ℕ → ℕ} (hI : ∀ o, I.TapeLocal o (k o))
    (τ τ' : ℕ → K) (s : Stmt Op) (ρ : Env) : Follows τ τ' (run I τ s ρ) (run I τ' s ρ) := by
  induction s generalizing ρ with
  | skip => exact fun a b h => by cases h; exact ⟨le_rfl, fun _ => rfl⟩
  | abort => exact fun a b h => by cases h
  | seq s t ihs iht => exact (ihs ρ).bind (iht ρ)
  | call o ds ins outs =>
    intro a b h
    obtain ⟨d, hd, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨i, hi, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨z, hz, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨h1, h2⟩ := (hI o).callS d i z τ τ' a b h
    exact ⟨h1, fun hag => by simp [run, hd, hi, hz, h2 hag]⟩
  | ite o ds ins t e iht ihe =>
    intro a b h
    obtain ⟨d, hd, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨i, hi, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨c, hc, h⟩ := Option.bind_eq_some_iff.mp h
    cases c with
    | false =>
      obtain ⟨h1, h2⟩ := ihe ρ a b (by simpa using h)
      exact ⟨h1, fun hag => by simp [run, hd, hi, hc, h2 hag]⟩
    | true =>
      obtain ⟨h1, h2⟩ := iht ρ a b (by simpa using h)
      exact ⟨h1, fun hag => by simp [run, hd, hi, hc, h2 hag]⟩
  | whileFuel fuel o ds ins body ih =>
    intro a b h
    obtain ⟨n, hn, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨d, hd, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨i, hi, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨h1, h2⟩ := Follows.whileIter (I.test o d i) (ih ρ) n a b h
    exact ⟨h1, fun hag => by simp [run, hn, hd, hi, h2 hag]⟩
  | bindIdx o ins bound body ih =>
    intro a b h
    obtain ⟨i, hi, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨B, hB, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨v, hv, h⟩ := Option.bind_eq_some_iff.mp h
    split_ifs at h with hle
    obtain ⟨h1, h2⟩ := ih _ a b h
    exact ⟨h1, fun hag => by simp [run, hi, hB, hv, hle, h2 hag]⟩
  | alloc len body ih =>
    intro a b h
    obtain ⟨n, hn, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨m₂, h₂, rfl⟩ := Option.map_eq_some_iff.mp h
    obtain ⟨h1, h2⟩ := ih _ _ m₂ h₂
    exact ⟨h1, fun hag => by simp [run, hn, h2 hag]⟩
  | loop n body ih =>
    intro a b h
    obtain ⟨c, hc, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨h1, h2⟩ := Follows.iter (fun i => ih (ρ.pushIdx i)) c a b h
    exact ⟨h1, fun hag => by simp [run, hc, h2 hag]⟩
  | frame ds args body ih =>
    intro a b h
    obtain ⟨d, hd, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨i, hi, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨h1, h2⟩ := ih _ a b h
    exact ⟨h1, fun hag => by simp [run, hd, hi, h2 hag]⟩

/-- A tree without tests and index binders: its uses of the tape are static. -/
def Stmt.Straight : Stmt Op → Prop
  | .skip => True
  | .abort => True
  | .seq s t => s.Straight ∧ t.Straight
  | .call _ _ _ _ => True
  | .ite _ _ _ _ _ => False
  | .whileFuel _ _ _ _ _ => False
  | .bindIdx _ _ _ _ => False
  | .alloc _ body => body.Straight
  | .loop _ body => body.Straight
  | .frame _ _ body => body.Straight

/-- **The static window** of a tree: the windows `k` of its calls, added up. -/
def staticWindow (k : Op → List ℕ → ℕ) : Stmt Op → List ℕ → ℕ
  | .seq s t, idx => staticWindow k s idx + staticWindow k t idx
  | .call o ds _ _, idx => ((IExp.evalList idx ds).map (k o)).getD 0
  | .alloc _ body, idx => staticWindow k body idx
  | .loop n body, idx =>
      ∑ i ∈ Finset.range ((n.eval idx).getD 0), staticWindow k body (idx ++ [i])
  | .frame ds args body, idx =>
      match IExp.evalList idx ds, IExp.evalList idx (args.map Operand.off) with
      | some d, some o => staticWindow k body (d ++ o)
      | _, _ => 0
  | _, _ => 0

theorem iter_pos {f : ℕ → Mem K → Option (Mem K)} {c : ℕ → ℕ}
    (h : ∀ i a b, f i a = some b → b.pos = a.pos + c i) {k : ℕ} {s s' : Mem K}
    (hk : iter f k s = some s') : s'.pos = s.pos + ∑ i ∈ Finset.range k, c i := by
  induction k generalizing s' with
  | zero => cases hk; simp
  | succ k ih =>
    obtain ⟨a, ha, hb⟩ := Option.bind_eq_some_iff.mp hk
    rw [h k a s' hb, ih ha, Finset.sum_range_succ, add_assoc]

/-- A tree without tests and index binders advances the tape by its static window. -/
theorem run_pos_of_straight {I : Interp Op K} {k : Op → List ℕ → ℕ}
    (hI : ∀ o, I.TapeLocal o (k o)) {τ : ℕ → K} {s : Stmt Op} (hs : s.Straight) {ρ : Env}
    {m m' : Mem K} (h : run I τ s ρ m = some m') : m'.pos = m.pos + staticWindow k s ρ.idx := by
  induction s generalizing ρ m m' with
  | skip => cases h; rfl
  | abort => cases h
  | seq s t ihs iht =>
    obtain ⟨a, ha, hb⟩ := Option.bind_eq_some_iff.mp h
    rw [iht hs.2 hb, ihs hs.1 ha, staticWindow, add_assoc]
  | call o ds ins outs =>
    obtain ⟨d, hd, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨i, hi, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨z, hz, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨m₁, h₁, hb⟩ := Option.bind_eq_some_iff.mp h
    split_ifs at hb
    cases hb
    simpa [staticWindow, hd] using (hI o d i z m τ τ fun _ _ => rfl).2 m' h₁
  | ite o ds ins t e iht ihe => exact hs.elim
  | whileFuel fuel o ds ins body ih => exact hs.elim
  | bindIdx o ins bound body ih => exact hs.elim
  | alloc len body ih =>
    obtain ⟨n, hn, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨m₂, h₂, rfl⟩ := Option.map_eq_some_iff.mp h
    simpa [staticWindow] using
      ih (ρ := ρ.pushBuf m.store.length) (m := ⟨m.store.push n, m.pos⟩) hs h₂
  | loop n body ih =>
    obtain ⟨c, hc, h⟩ := Option.bind_eq_some_iff.mp h
    simpa [staticWindow, hc] using iter_pos (fun i a b hb => ih hs hb) h
  | frame ds args body ih =>
    obtain ⟨d, hd, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨i, hi, h⟩ := Option.bind_eq_some_iff.mp h
    simpa [staticWindow, hd, Operand.offs_of_evalList hi] using ih hs h

/-- **The window lemma.** The meaning induced by an implementation without tests and index
binders over tape-local operations is tape-local, with the static window of the tree. -/
theorem Interp.TapeLocal.link {I : Interp Op₂ K} {k₂ : Op₂ → List ℕ → ℕ}
    (hI : ∀ o, I.TapeLocal o (k₂ o)) {T : Table Op₁ Op₂} {o : Op₁} {R : Impl Op₂}
    (hT : T o = .inl R) (hs : R.body.Straight) {w : List ℕ → ℕ}
    (hw : ∀ d offs : List ℕ, d.length = R.nd → offs.length = R.nin + R.nout →
      staticWindow k₂ R.body (d ++ offs) = w d) : (I.link T).TapeLocal o w := by
  intro d ins outs m τ τ' hag
  simp only [Interp.link, hT]
  split_ifs with hfit
  swap
  · exact ⟨rfl, fun m' h => by cases h⟩
  have hw' := hw d ((ins ++ outs).map Prod.snd) hfit.1 (by simp [hfit.2.1, hfit.2.2])
  have key : ∀ (σ σ' : ℕ → K) (m' : Mem K),
      (∀ j < w d, σ (m.pos + j) = σ' (m.pos + j)) →
      run I σ R.body (Env.frame d (ins ++ outs)) m = some m' →
      m'.pos = m.pos + w d ∧ run I σ' R.body (Env.frame d (ins ++ outs)) m = some m' := by
    intro σ σ' m' hσ hr
    have hp : m'.pos = m.pos + w d := by rw [run_pos_of_straight hI hs hr, Env.idx_frame, hw']
    refine ⟨hp, (run_follows hI σ σ' _ _ m m' hr).2 fun j hj hj' => ?_⟩
    have := hσ (j - m.pos) (by omega)
    rwa [Nat.add_sub_cancel' hj] at this
  refine ⟨?_, fun m' h => (key τ τ' m' hag h).1⟩
  cases hr : run I τ R.body (Env.frame d (ins ++ outs)) m with
  | some m' => exact (key τ τ' m' hag hr).2.symm
  | none =>
    cases hr' : run I τ' R.body (Env.frame d (ins ++ outs)) m with
    | none => rfl
    | some m' =>
      rw [(key τ' τ m' (fun j hj => (hag j hj).symm) hr').2] at hr
      cases hr

/-- A kept operation keeps its window. -/
theorem Interp.TapeLocal.link_kept {I : Interp Op₂ K} {T : Table Op₁ Op₂} {o : Op₁} {o' : Op₂}
    (hT : T o = .inr o') {k : List ℕ → ℕ} (h : I.TapeLocal o' k) : (I.link T).TapeLocal o k := by
  intro d ins outs m τ τ' hag
  simp only [Interp.link, hT]
  exact h d ins outs m τ τ' hag

/-- Block functions are tape-local with their window. -/
theorem Interp.ofFns_tapeLocal (F : Op → BlockFn K) (o : Op) :
    (Interp.ofFns F).TapeLocal o (F o).win := by
  intro d ins outs m τ τ' hag
  have hmap : ((List.range ((F o).win d)).map fun j => τ (m.pos + j)) =
      (List.range ((F o).win d)).map fun j => τ' (m.pos + j) :=
    List.map_congr_left fun j hj => hag j (List.mem_range.mp hj)
  rcases outs with _ | ⟨z, _ | ⟨z', outs⟩⟩
  · exact ⟨rfl, fun m' h => by cases h⟩
  · simp only [Interp.ofFns, BlockFn.apply, hmap, true_and]
    intro m' h
    obtain ⟨xs, -, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨ys, -, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨m₁, h₁, rfl⟩ := Option.map_eq_some_iff.mp h
    simp [(Mem.shape_of_write h₁).2]
  · exact ⟨rfl, fun m' h => by cases h⟩

end NLAlib.Ops
