/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Logic
public import NLAlib.Ops.StoreSimp

/-!
# Rules on given operands, and rules for loops whose length is not a size

## Main results

* Calls on given operands. `NLAlib.Ops.wp_call_rel`: a call of an operation under a relational
  contract in operand form (`NLAlib.Ops.BlockRel`), from the blocks that are read; the
  continuation receives the output block and its relation to them, with nothing to identify
  again. `NLAlib.Ops.wp_call_fn_read`: the same for a functional contract.
  `NLAlib.Ops.Interp.link_meets_rel`: grounding a relational contract in operand form.
* `NLAlib.Ops.wp_whileFuel`: total correctness of a `whileFuel` loop, with an invariant on the
  memory indexed by the number of rounds done and a bound `J` on the rounds that comes from the
  mathematics (the fuel only has to be at least `J`). `NLAlib.Ops.wp_whileFuel_liberal`: partial
  correctness, with an invariant and no bound.
* `NLAlib.Ops.wp_ifZero`, `NLAlib.Ops.wp_ifPos`: branches on a size.
-/

@[expose] public section

namespace NLAlib.Ops

variable {Op Op₁ Op₂ Tst K : Type}

section Rules

variable {md : Mode} {I : Interp Op Tst K} {τ : Tape K} {ρ : Env} {Q : Mem K → Prop} {m : Mem K}

/-- **Call under a relational contract, on given operands**: the input blocks `xs` are read, the
output block `ys` has the declared length and is related to `xs`. -/
theorem wp_call_rel {o : Op} {R : BlockRel K} {adm : List ℕ → List (ℕ × ℕ) → ℕ × ℕ → Prop}
    (hI : I.Meets md o (R.spec adm)) {ds : List IExp} {ins outs : List Operand} {d : List ℕ}
    {a : List (ℕ × ℕ)} {z : ℕ × ℕ} (hd : IExp.evalList ρ.idx ds = some d)
    (ha : Operand.evalList ρ ins = some a) (hb : Operand.evalList ρ outs = some [z])
    (hnd : d.length = R.nd) (hadm : adm d a z) (hl : m.Live (a ++ [z])) {xs : List (List K)}
    (hr : m.readBlocks a (R.inLens d) = some xs) (hz : z.2 + R.outLen d ≤ m.store.len z.1)
    (hQ : ∀ ys, ys.length = R.outLen d → R.rel d xs ys → Q (m.updBlock z ys)) :
    Wp md I τ (.call o ds ins outs) ρ Q m := by
  refine wp_call hI hd ha hb ⟨z, rfl, hnd, hadm, fun _ => ⟨hl, by simp [hr], hz⟩⟩ ?_
  rintro m' ⟨z', xs', ys, hz', hr', hl', hrel, rfl⟩
  cases hz'
  rw [hr] at hr'
  cases hr'
  exact hQ ys hl' hrel

/-- **Call under a relational contract whose output is one cell.** -/
theorem wp_call_rel_cell {o : Op} {R : BlockRel K}
    {adm : List ℕ → List (ℕ × ℕ) → ℕ × ℕ → Prop} (hI : I.Meets md o (R.spec adm))
    {ds : List IExp} {ins outs : List Operand} {d : List ℕ} {a : List (ℕ × ℕ)} {z : ℕ × ℕ}
    (hd : IExp.evalList ρ.idx ds = some d) (ha : Operand.evalList ρ ins = some a)
    (hb : Operand.evalList ρ outs = some [z]) (hnd : d.length = R.nd) (hone : R.outLen d = 1)
    (hadm : adm d a z) (hl : m.Live (a ++ [z])) {xs : List (List K)}
    (hr : m.readBlocks a (R.inLens d) = some xs) (hz : z.2 < m.store.len z.1)
    (hQ : ∀ v, R.rel d xs [v] → Q (m.upd z v)) : Wp md I τ (.call o ds ins outs) ρ Q m := by
  refine wp_call_rel hI hd ha hb hnd hadm hl hr (by omega) fun ys hys hrel => ?_
  obtain ⟨v, rfl⟩ := List.length_eq_one_iff.mp (hys.trans hone)
  exact hQ v hrel

/-- **Call of a functional operation, on given operands**: from the blocks that are read. -/
theorem wp_call_fn_read {o : Op} {f : BlockFn K} {adm : List ℕ → List (ℕ × ℕ) → ℕ × ℕ → Prop}
    (hI : I.IsFn .total o f adm) {ds : List IExp} {ins outs : List Operand} {d : List ℕ}
    {a : List (ℕ × ℕ)} {z : ℕ × ℕ} (hd : IExp.evalList ρ.idx ds = some d)
    (ha : Operand.evalList ρ ins = some a) (hb : Operand.evalList ρ outs = some [z])
    (hadm : adm d a z) (hl : m.Live (a ++ [z])) {xs : List (List K)} {ys : List K}
    (hr : m.readBlocks a (f.inLens d) = some xs)
    (hfn : f.fn d (τ.window f.stream m.pos (f.win d)) xs = some ys)
    (hz : z.2 + ys.length ≤ m.store.len z.1) (hQ : Q ((m.updBlock z ys).advance (f.win d))) :
    Wp md I τ (.call o ds ins outs) ρ Q m :=
  wp_call_fn hI hd ha hb hadm (BlockFn.apply_of_read hl hr hfn hz) hQ

/-! ### Loops whose length is not a size -/

theorem whileIter_total {test : Mem K → Option Bool} {body : Mem K → Option (Mem K)}
    (Inv : ℕ → Mem K → Prop) {J : ℕ}
    (htest : ∀ i m, Inv i m → ∃ c, test m = some c ∧ (c = true → i < J))
    (hbody : ∀ i m, Inv i m → test m = some true → ∃ m', body m = some m' ∧ Inv (i + 1) m') :
    ∀ (r i : ℕ) (m : Mem K), i ≤ J → J - i ≤ r → Inv i m →
      ∃ j m', j ≤ J ∧ whileIter test id body r m = some m' ∧ Inv j m' ∧ test m' = some false := by
  intro r
  induction r with
  | zero =>
    intro i m hiJ hr hi
    obtain ⟨c, hc, hlt⟩ := htest i m hi
    cases c with
    | true => exact absurd (hlt rfl) (by omega)
    | false => exact ⟨i, m, hiJ, by simp [whileIter, hc], hi, hc⟩
  | succ r ih =>
    intro i m hiJ hr hi
    obtain ⟨c, hc, hlt⟩ := htest i m hi
    cases c with
    | false => exact ⟨i, m, hiJ, by simp [whileIter, hc], hi, hc⟩
    | true =>
      have := hlt rfl
      obtain ⟨m₁, hb, hi₁⟩ := hbody i m hi hc
      obtain ⟨j, m', hj, hrun, hinv, hf⟩ := ih (i + 1) m₁ (by omega) (by omega) hi₁
      exact ⟨j, m', hj, by simp [whileIter, hc, hb, hrun], hinv, hf⟩

/-- **A loop while a test holds, total correctness.** `Inv i` is an invariant of the memory after
`i` rounds; the test is defined under it and can hold only while `i < J`. The bound `J` comes
from the mathematics of the decoded state; the fuel only has to be at least `J`. -/
theorem wp_whileFuel {fuel : IExp} {q : Tst} {ds : List IExp} {ins : List Operand}
    {body : Stmt Op Tst} {k : ℕ} {d : List ℕ} {a : List (ℕ × ℕ)}
    (hk : fuel.eval ρ.idx = some k) (hd : IExp.evalList ρ.idx ds = some d)
    (ha : Operand.evalList ρ ins = some a) (Inv : ℕ → Mem K → Prop) (J : ℕ) (hJ : J ≤ k)
    (h0 : Inv 0 m) (htest : ∀ i m, Inv i m → ∃ c, I.test q d a m = some c ∧ (c = true → i < J))
    (hbody : ∀ i m, Inv i m → I.test q d a m = some true →
      Wp .total I τ body ρ (Inv (i + 1)) m)
    (hQ : ∀ i m, i ≤ J → Inv i m → I.test q d a m = some false → Q m) :
    Wp md I τ (.whileFuel fuel q ds ins body) ρ Q m := by
  obtain ⟨j, m', hj, hrun, hinv, hf⟩ :=
    whileIter_total Inv htest hbody k 0 m (Nat.zero_le _) (by omega) h0
  exact wp_of_run (by simp only [run, hk, hd, ha, Option.bind_some, hrun]) (hQ j m' hj hinv hf)

theorem whileIter_liberal {test : Mem K → Option Bool} {body : Mem K → Option (Mem K)}
    (Inv : Mem K → Prop) (hbody : ∀ m m', Inv m → test m = some true → body m = some m' → Inv m') :
    ∀ (r : ℕ) (m m' : Mem K), Inv m → whileIter test id body r m = some m' →
      Inv m' ∧ test m' = some false := by
  intro r
  induction r with
  | zero =>
    intro m m' hi h
    obtain ⟨c, hc, h⟩ := Option.bind_eq_some_iff.mp h
    cases c with
    | true => simp at h
    | false =>
      simp only [Bool.false_eq_true, if_false, id, Option.some.injEq] at h
      exact h ▸ ⟨hi, hc⟩
  | succ r ih =>
    intro m m' hi h
    obtain ⟨c, hc, h⟩ := Option.bind_eq_some_iff.mp h
    cases c with
    | false =>
      simp only [Bool.false_eq_true, if_false, id, Option.some.injEq] at h
      exact h ▸ ⟨hi, hc⟩
    | true =>
      simp only [if_true, id] at h
      obtain ⟨m₁, hb, h⟩ := Option.bind_eq_some_iff.mp h
      exact ih m₁ m' (hbody m m₁ hi hc hb) h

/-- **A loop while a test holds, partial correctness**: an invariant, and no bound. -/
theorem wp_whileFuel_liberal {fuel : IExp} {q : Tst} {ds : List IExp} {ins : List Operand}
    {body : Stmt Op Tst} {d : List ℕ} {a : List (ℕ × ℕ)}
    (hd : IExp.evalList ρ.idx ds = some d) (ha : Operand.evalList ρ ins = some a)
    (Inv : Mem K → Prop) (h0 : Inv m)
    (hbody : ∀ m, Inv m → I.test q d a m = some true → Wp .liberal I τ body ρ Inv m)
    (hQ : ∀ m, Inv m → I.test q d a m = some false → Q m) :
    Wp .liberal I τ (.whileFuel fuel q ds ins body) ρ Q m := by
  intro m' hrun
  simp only [run, hd, ha, Option.bind_some] at hrun
  obtain ⟨k, -, hrun⟩ := Option.bind_eq_some_iff.mp hrun
  obtain ⟨hi, hf⟩ := whileIter_liberal Inv (fun m m₁ hi hc hb => hbody m hi hc m₁ hb) k m m' h0
    hrun
  exact hQ m' hi hf

/-! ### Branches on a size -/

/-- A branch on a size being zero. -/
theorem wp_ifZero {e : IExp} {body : Stmt Op Tst} {n : ℕ} (he : e.eval ρ.idx = some n)
    (h : if n = 0 then Wp md I τ body (ρ.pushIdx 0) Q m else Q m) :
    Wp md I τ (.ifZero e body) ρ Q m := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [if_pos rfl] at h
    simpa [Wp, Stmt.ifZero, run, he, iter] using h
  · rw [if_neg (by omega)] at h
    have h1 : 1 - n = 0 := by omega
    simpa [Wp, Stmt.ifZero, run, he, h1, iter] using Mode.holds_some (md := md) h

/-- A branch on a size being positive. -/
theorem wp_ifPos {e : IExp} {body : Stmt Op Tst} {n : ℕ} (he : e.eval ρ.idx = some n)
    (h : if 0 < n then Wp md I τ body (ρ.pushIdx 0) Q m else Q m) :
    Wp md I τ (.ifPos e body) ρ Q m := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [if_neg (lt_irrefl 0)] at h
    simpa [Wp, Stmt.ifPos, run, he, iter] using Mode.holds_some (md := md) h
  · rw [if_pos hn] at h
    have h1 : 1 - (1 - n) = 1 := by omega
    simpa [Wp, Stmt.ifPos, run, he, h1, iter] using h

end Rules

/-! ### Grounding a relational contract in operand form -/

/-- **The implementation `R` meets the relational contract `B`** over the interpretation `I`: on
admitted, live operands, with the input blocks `xs` read and room for the output, it fits and its
run writes an output block related to `xs` and nothing else. This is the certificate of an
implementation, independent of any table. -/
def Impl.MeetsRel (R : Impl Op Tst) (I : Interp Op Tst K) (B : BlockRel K)
    (adm : List ℕ → List (ℕ × ℕ) → ℕ × ℕ → Prop) : Prop :=
  ∀ (d : List ℕ) (ins : List (ℕ × ℕ)) (z : ℕ × ℕ) (τ : Tape K) (m : Mem K) (xs : List (List K)),
    d.length = B.nd → adm d ins z → m.Live (ins ++ [z]) →
    m.readBlocks ins (B.inLens d) = some xs → z.2 + B.outLen d ≤ m.store.len z.1 →
    R.Fits d.length ins.length 1 ∧ Wp .total I τ R.body (Env.frame d (ins ++ [z]))
      (fun m' => ∃ ys, ys.length = B.outLen d ∧ B.rel d xs ys ∧ m' = m.updBlock z ys) m

/-- **Grounding a relational contract in operand form**: the induced interpretation meets the
contract of an operation whose implementation meets it. -/
theorem Interp.link_meets_rel {I : Interp Op₂ Tst K} {T : Table Op₁ Op₂ Tst} {o : Op₁}
    {R : Impl Op₂ Tst} (hT : T o = .inl R) {B : BlockRel K}
    {adm : List ℕ → List (ℕ × ℕ) → ℕ × ℕ → Prop} (h : R.MeetsRel I B adm) :
    (I.link T).Meets .total o (B.spec adm) := by
  refine Interp.link_meets hT ?_
  rintro d ins outs τ m ⟨z, rfl, hnd, hadm, hn⟩
  obtain ⟨hl, hr, hz⟩ := hn rfl
  obtain ⟨xs, hxs⟩ := Option.isSome_iff_exists.mp hr
  obtain ⟨hfit, hw⟩ := h d ins z τ m xs hnd hadm hl hxs hz
  exact ⟨fun _ => hl, fun _ => ⟨hfit, hw.mono fun m' ⟨ys, h1, h2, h3⟩ =>
    ⟨z, xs, ys, rfl, hxs, h1, h2, h3⟩⟩⟩

/-- **A functional operation meets a relational contract that its values satisfy.** For
witnesses and model primitives: the block function has no window and the lengths of the
relation, and on blocks that were read its value has the declared length and is related to
them. -/
theorem Interp.IsFn.meets_rel {I : Interp Op Tst K} {o : Op} {f : BlockFn K}
    {adm' : List ℕ → List (ℕ × ℕ) → ℕ × ℕ → Prop} (h : I.IsFn .total o f adm') {R : BlockRel K}
    {adm : List ℕ → List (ℕ × ℕ) → ℕ × ℕ → Prop} (hadm : ∀ d ins z, adm d ins z → adm' d ins z)
    (hwin : ∀ d, f.win d = 0) (hin : ∀ d, f.inLens d = R.inLens d)
    (hf : ∀ d w xs (m : Mem K) ins z, d.length = R.nd → adm d ins z →
      m.readBlocks ins (R.inLens d) = some xs →
      ∃ ys, f.fn d w xs = some ys ∧ ys.length = R.outLen d ∧ R.rel d xs ys) :
    I.Meets .total o (R.spec adm) := by
  rintro d ins outs τ m ⟨z, rfl, hnd, hadm', hn⟩
  obtain ⟨hl, hr, hz⟩ := hn rfl
  obtain ⟨xs, hxs⟩ := Option.isSome_iff_exists.mp hr
  obtain ⟨ys, hys, hlen, hrel⟩ := hf d _ xs m ins z hnd hadm' hxs
  have ha := BlockFn.apply_of_read (f := f) (τ := τ) hl (by rw [hin]; exact hxs) hys
    (by rw [hlen]; exact hz)
  rw [hwin] at ha
  exact ⟨_, h.callS_eq (hadm _ _ _ hadm') ha, z, xs, ys, rfl, hxs, hlen, hrel, rfl⟩

/-- A kept operation meets the relational contracts it meets below. -/
theorem Interp.link_meets_rel_kept {I : Interp Op₂ Tst K} {T : Table Op₁ Op₂ Tst} {o : Op₁}
    {o' : Op₂} (hT : T o = .inr o') {md : Mode} {C : Contract K} (h : I.Meets md o' C) :
    (I.link T).Meets md o C := Interp.link_meets_kept hT h

end NLAlib.Ops
