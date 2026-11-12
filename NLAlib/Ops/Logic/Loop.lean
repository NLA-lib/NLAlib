/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Logic.Writes
public import NLAlib.Ops.Logic.Layout

/-!
# Loop rules with footprints

Every loop rule here has the **standard invariant form**: a family of footprints `F i` (what
the first `i` rounds may write, increasing in `i`) and a family of postconditions `P i`. A round
is proved from a fresh memory `m'` with the frame `m.store.EqOff (F i) m'.store` and `P i m'`,
and must write only `F (i + 1)` from `m'`; the rule composes the frames. So a round never writes
an `EqOff` chain from the start of the loop, and the invariant never says `∃ s', m' = ⟨s', _⟩`.

## Main results

* `NLAlib.Ops.writes_loop`: the counted loop.
* `NLAlib.Ops.writes_loop₂`: two nested counted loops, with an invariant indexed by the row and
  the column (no quotient or remainder of a linear index).
* `NLAlib.Ops.writes_fill`, `NLAlib.Ops.writes_fill₂`: a loop (two loops) that fills a vector
  (a matrix in a layout) one entry per round, with the position of the tape moving; the round
  only has to prove the one cell it writes.
* `NLAlib.Ops.writes_fillRel`, `NLAlib.Ops.writes_fillRel₂`: the same when the values are known
  only by a relation (the outputs of relational calls: `gemm`, coefficients).
* `NLAlib.Ops.writes_whileFuel`: the loop with early exit.
* `NLAlib.Ops.writes_ifPos`, `NLAlib.Ops.writes_ifZero`: branches on a size.
-/

@[expose] public section

namespace NLAlib.Ops

variable {Op Tst K : Type} {md : Mode} {I : Interp Op Tst K} {τ : Tape K} {ρ : Env}
  {m : Mem K}

/-- A footprint family increasing up to `N` is increasing from `0`. -/
theorem Fp.le_of_chain {G : ℕ → Fp} {N : ℕ} (hG : ∀ i < N, G i ≤ G (i + 1)) :
    ∀ i j, i ≤ j → j ≤ N → G i ≤ G j := by
  intro i j hij hjN
  induction j with
  | zero => obtain rfl : i = 0 := by omega
            exact le_rfl
  | succ j ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp (Nat.lt_succ_of_le hij) with h | h
    · exact (ih (by omega) (by omega)).trans (hG j (by omega))
    · rw [h]

/-- An index expression evaluates the same after more variables are bound. -/
theorem IExp.eval_append {e : IExp} {idx : List ℕ} {v : ℕ} (h : e.eval idx = some v)
    (l : List ℕ) : e.eval (idx ++ l) = some v := by
  induction e generalizing v with
  | var i =>
    simp only [IExp.eval] at h ⊢
    obtain ⟨hi, -⟩ := List.getElem?_eq_some_iff.mp h
    rw [List.getElem?_append_left hi]
    exact h
  | const n => exact h
  | add a b iha ihb | mul a b iha ihb | sub a b iha ihb | div a b iha ihb =>
    simp only [IExp.eval] at h ⊢
    cases ha : a.eval idx with
    | none => simp [ha] at h
    | some x => cases hb : b.eval idx with
      | none => simp [ha, hb] at h
      | some y =>
        simp only [ha, hb] at h
        rw [iha ha, ihb hb]
        exact h

/-- **The counted loop**, in the standard invariant form. -/
theorem writes_loop {n : IExp} {body : Stmt Op Tst} {N : ℕ} (hn : n.eval ρ.idx = some N)
    (F : ℕ → Fp) (hF : ∀ i < N, F i ≤ F (i + 1)) (P : ℕ → Mem K → Prop) (h0 : P 0 m)
    (hstep : ∀ i < N, ∀ m', m.store.EqOff (F i) m'.store → P i m' →
      Writes md I τ body (ρ.pushIdx i) (F (i + 1)) (P (i + 1)) m') :
    Writes md I τ (.loop n body) ρ (F N) (P N) m :=
  wp_loop hn (fun i m' => m.store.EqOff (F i) m'.store ∧ P i m') ⟨Store.EqOff.refl _ _, h0⟩
    (fun i hi m' hm => Wp.mono (hstep i hi m' hm.1 hm.2) fun _ hm' =>
      ⟨(hm.1.mono (hF i hi)).trans hm'.1, hm'.2⟩) fun _ h => h

/-- Dimensions already evaluable in a context retain their values under fresh index binders. -/
theorem IExp.evalList_append {idx : List ℕ} {es : List IExp} {vs : List ℕ}
    (h : IExp.evalList idx es = some vs) (extra : List ℕ) :
    IExp.evalList (idx ++ extra) es = some vs := by
  induction es generalizing vs with
  | nil => cases h; rfl
  | cons e es ih =>
    rw [IExp.evalList_cons] at h ⊢
    obtain ⟨v, hv, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨vs, hvs, rfl⟩ := Option.map_eq_some_iff.mp h
    rw [IExp.eval_append hv, ih hvs]
    rfl

/-- A fresh loop index cannot change an operand that already resolves in the parent context. -/
theorem Operand.eval_pushIdx {ρ : Env} {a : Operand} {v : ℕ × ℕ}
    (h : a.eval ρ = some v) (i : ℕ) : a.eval (ρ.pushIdx i) = some v := by
  rw [Operand.eval_eq] at h ⊢
  obtain ⟨b, hb, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨off, hoff, rfl⟩ := Option.map_eq_some_iff.mp h
  simp only [Env.buf_pushIdx, Env.idx_pushIdx, hb, Option.bind_some]
  rw [IExp.eval_append hoff]
  rfl

/-- A fixed framed operand list is independent of the fresh loop index. -/
theorem Operand.evalList_pushIdx {ρ : Env} {as : List Operand} {vs : List (ℕ × ℕ)}
    (h : Operand.evalList ρ as = some vs) (i : ℕ) :
    Operand.evalList (ρ.pushIdx i) as = some vs := by
  induction as generalizing vs with
  | nil => cases h; rfl
  | cons a as ih =>
    rw [Operand.evalList_cons] at h ⊢
    obtain ⟨v, hv, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨vs, hvs, rfl⟩ := Option.map_eq_some_iff.mp h
    rw [Operand.eval_pushIdx hv, ih hvs]
    rfl

/-- A framed state transition composes into mathematical iteration. Clients supply the stored
state predicate, its transition and the valid executed states; liveness, binder stability,
position chaining and the loop invariant are shared here. The frame from the initial store is
forwarded to each round for any additional capacity or input facts it needs. -/
theorem writes_loop_frame_iterate {S : Type} {n : IExp} {N : ℕ}
    {ds : List IExp} {args : List Operand} {body : Stmt Op Tst}
    {d : List ℕ} {a : List (ℕ × ℕ)} {F : Fp} (State : S → Mem K → Prop)
    (transition : S → S) (valid : S → Prop) {s : S}
    (hn : n.eval ρ.idx = some N) (hd : IExp.evalList ρ.idx ds = some d)
    (ha : Operand.evalList ρ args = some a) (hl : m.Live a) (hs : State s m)
    (hvalid : ∀ i < N, valid (transition^[i] s))
    (hstep : ∀ s' m', m.store.EqOff F m'.store → m'.Live a → State s' m' → valid s' →
      Writes md I τ body (Env.frame d a) F
        (fun m'' => m''.pos = m'.pos ∧ State (transition s') m'') m') :
    Writes md I τ (.loop n (.frame ds args body)) ρ F
      (fun m' => m'.pos = m.pos ∧ State (transition^[N] s) m') m := by
  refine writes_loop hn (fun _ => F) (fun _ _ => le_rfl)
    (fun i m' => m'.pos = m.pos ∧ State (transition^[i] s) m') ⟨rfl, hs⟩
    fun i hi m' hfr ⟨hpos, hstate⟩ => ?_
  refine (writes_frame (IExp.evalList_append hd [i]) (Operand.evalList_pushIdx ha i)
    (hl.congr hfr.length_eq) (hstep _ m' hfr (hl.congr hfr.length_eq) hstate (hvalid i hi))).mono
    le_rfl ?_
  intro m'' _ ⟨hpos', hstate'⟩
  exact ⟨hpos'.trans hpos, by simpa only [Function.iterate_succ_apply'] using hstate'⟩

/-- **Two nested counted loops**, with an invariant indexed by the row `i` and the column `j`;
the end of a row is the start of the next (`hnext`). -/
theorem writes_loop₂ {n₁ n₂ : IExp} {body : Stmt Op Tst} {M N : ℕ}
    (hn₁ : n₁.eval ρ.idx = some M) (hn₂ : ∀ i, n₂.eval (ρ.pushIdx i).idx = some N)
    (F : ℕ → ℕ → Fp) (hF : ∀ i < M, ∀ j < N, F i j ≤ F i (j + 1))
    (hrow : ∀ i < M, F i N ≤ F (i + 1) 0) (P : ℕ → ℕ → Mem K → Prop) (h0 : P 0 0 m)
    (hnext : ∀ i < M, ∀ m', P i N m' → P (i + 1) 0 m')
    (hstep : ∀ i < M, ∀ j < N, ∀ m', m.store.EqOff (F i j) m'.store → P i j m' →
      Writes md I τ body ((ρ.pushIdx i).pushIdx j) (F i (j + 1)) (P i (j + 1)) m') :
    Writes md I τ (.loop n₁ (.loop n₂ body)) ρ (F M 0) (P M 0) m := by
  refine writes_loop hn₁ (fun i => F i 0) (fun i hi => (Fp.le_of_chain (hF i hi) 0 N (by omega)
    le_rfl).trans (hrow i hi)) (fun i => P i 0) h0 fun i hi m' hfr hp => ?_
  refine Writes.mono (writes_loop (hn₂ i) (fun j => F i j) (hF i hi)
    (fun j m'' => m.store.EqOff (F i j) m''.store ∧ P i j m'') ⟨hfr, hp⟩
    fun j hj m'' _ hm => Writes.mono (hstep i hi j hj m'' hm.1 hm.2) le_rfl
      fun _ hfr' hp' => ⟨(hm.1.mono (hF i hi j hj)).trans hfr', hp'⟩) (hrow i hi)
    fun _ _ hm => hnext i hi _ hm.2

/-- **The loop that fills a vector**: round `i` writes `v i` in the cell `o + i` of `b` and
moves the position from `pos i` to `pos (i + 1)`; it may read the entries already written and
everything off the block. -/
theorem writes_fill {n : IExp} {body : Stmt Op Tst} {N b o : ℕ} (hn : n.eval ρ.idx = some N)
    (v : ℕ → K) (pos : ℕ → ℕ) (hpos : m.pos = pos 0)
    (hstep : ∀ i < N, ∀ m', m.store.EqOff (Store.inBlock b o i) m'.store →
      m'.store.HoldsVec b o i v → m'.pos = pos i →
      Writes md I τ body (ρ.pushIdx i) (Store.inBlock b (o + i) 1)
        (fun m'' => m''.store.get b (o + i) = some (v i) ∧ m''.pos = pos (i + 1)) m') :
    Writes md I τ (.loop n body) ρ (Store.inBlock b o N)
      (fun m' => m'.store.HoldsVec b o N v ∧ m'.pos = pos N) m :=
  writes_loop hn (fun i => Store.inBlock b o i)
    (fun i _ => Fp.inBlock_le_inBlock le_rfl (by omega))
    (fun i m' => m'.store.HoldsVec b o i v ∧ m'.pos = pos i)
    ⟨fun _ h => absurd h (Nat.not_lt_zero _), hpos⟩ fun i hi m' hfr hm =>
      Writes.mono (hstep i hi m' hfr hm.1 hm.2) (Fp.inBlock_le_inBlock (by omega) (by omega))
        fun m'' hfr' hm' => ⟨Store.HoldsVec.snoc (hfr'.keep (Store.readsOnly_holdsVec b o i v)
          (fun _ _ h₁ h₂ => by obtain ⟨-, h₁, -⟩ := h₁; obtain ⟨-, -, h₂⟩ := h₂; omega) hm.1)
          hm'.1, hm'.2⟩

/-- **The two loops that fill a matrix by columns** in the layout `L`: round `(j, i)` writes the
entry `A i j` in its cell and moves the position from `pos (j * rows + i)` to the next. The
2-D form of `writes_fill` (the fill of a Gaussian test matrix from the tape). -/
theorem writes_fill₂ {n₁ n₂ : IExp} {body : Stmt Op Tst} (L : MatLayout) (hL : L.Valid)
    (hn₁ : n₁.eval ρ.idx = some L.cols) (hn₂ : ∀ j, n₂.eval (ρ.pushIdx j).idx = some L.rows)
    (A : ℕ → ℕ → K) (pos : ℕ → ℕ) (hpos : m.pos = pos 0)
    (hstep : ∀ j < L.cols, ∀ i < L.rows, ∀ m', m.store.EqOff (L.upto j i) m'.store →
      m'.store.HoldsMatUpto L A j i → m'.pos = pos (j * L.rows + i) →
      Writes md I τ body ((ρ.pushIdx j).pushIdx i) (Store.inBlock L.buf (L.cell i j) 1)
        (fun m'' => m''.store.get L.buf (L.cell i j) = some (A i j) ∧
          m''.pos = pos (j * L.rows + i + 1)) m') :
    Writes md I τ (.loop n₁ (.loop n₂ body)) ρ L.fp
      (fun m' => m'.store.HoldsMat L A ∧ m'.pos = pos (L.cols * L.rows)) m := by
  have h := writes_loop₂ (P := fun j i m' => m'.store.HoldsMatUpto L A j i ∧
      m'.pos = pos (j * L.rows + i)) hn₁ hn₂ (fun j i => L.upto j i)
    (fun j _ i _ => by rw [MatLayout.upto_succ]; exact le_sup_left)
    (fun j _ => by rw [MatLayout.upto_col])
    ⟨⟨fun _ _ _ h => absurd h (Nat.not_lt_zero _), fun _ h => absurd h (Nat.not_lt_zero _)⟩,
      by simpa using hpos⟩
    (fun j _ m' hm => ⟨⟨fun i' hi' j' hj' => by
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj' with hj' | rfl
        · exact hm.1.1 i' hi' j' hj'
        · exact hm.1.2 i' hi', fun _ h => absurd h (Nat.not_lt_zero _)⟩,
      by rw [hm.2, Nat.succ_mul, Nat.add_zero]⟩)
    fun j hj i hi m' hfr hm => Writes.mono (hstep j hj i hi m' hfr hm.1 hm.2)
      (by rw [MatLayout.upto_succ]; exact le_sup_right) fun m'' hfr' hm' => ⟨⟨?_, ?_⟩, hm'.2⟩
  · rw [MatLayout.upto_cols] at h
    exact Writes.mono h le_rfl fun _ _ hm => ⟨Store.holdsMatUpto_cols.mp hm.1, by
      rw [hm.2, Nat.add_zero]⟩
  · intro i' hi' j' hj'
    rw [hfr'.get_eq fun hc => ?_]
    · exact hm.1.1 i' hi' j' hj'
    · obtain ⟨-, h1, h2⟩ := hc
      have := Idx.mul_add_le_mul hj' L.ld
      unfold MatLayout.Valid at hL
      simp only [MatLayout.cell] at h1 h2
      have := Nat.mul_le_mul_right L.ld (show j' + 1 ≤ j by omega)
      rw [Nat.succ_mul] at this
      omega
  · intro i' hi'
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi' with hi' | rfl
    · rw [hfr'.get_eq fun hc => ?_]
      · exact hm.1.2 i' hi'
      · obtain ⟨-, h1, h2⟩ := hc
        simp only [MatLayout.cell] at h1 h2
        omega
    · exact hm'.1

/-- **The loop that fills a vector with values known only by a relation** (the outputs of
relational calls): round `i` writes some `x` with `R i x` in the cell `o + i`; at the end the
block holds a vector all of whose entries satisfy `R`. The fill pattern of `gemm`, of the
coefficients of Gram–Schmidt, of a loop of dot products. -/
theorem writes_fillRel [Nonempty K] {n : IExp} {body : Stmt Op Tst} {N b o : ℕ}
    (hn : n.eval ρ.idx = some N) (R : ℕ → K → Prop) (pos : ℕ → ℕ) (hpos : m.pos = pos 0)
    (hstep : ∀ i < N, ∀ m', m.store.EqOff (Store.inBlock b o i) m'.store →
      (∃ v : ℕ → K, m'.store.HoldsVec b o i v ∧ ∀ i' < i, R i' (v i')) → m'.pos = pos i →
      Writes md I τ body (ρ.pushIdx i) (Store.inBlock b (o + i) 1)
        (fun m'' => (∃ x, m''.store.get b (o + i) = some x ∧ R i x) ∧ m''.pos = pos (i + 1)) m') :
    Writes md I τ (.loop n body) ρ (Store.inBlock b o N)
      (fun m' => (∃ v : ℕ → K, m'.store.HoldsVec b o N v ∧ ∀ i < N, R i (v i)) ∧
        m'.pos = pos N) m := by
  refine writes_loop hn (fun i => Store.inBlock b o i)
    (fun i _ => Fp.inBlock_le_inBlock le_rfl (by omega))
    (fun i m' => (∃ v : ℕ → K, m'.store.HoldsVec b o i v ∧ ∀ i' < i, R i' (v i')) ∧
      m'.pos = pos i)
    ⟨⟨fun _ => Classical.arbitrary K, fun _ h => absurd h (Nat.not_lt_zero _),
      fun _ h => absurd h (Nat.not_lt_zero _)⟩, hpos⟩ fun i hi m' hfr hm => ?_
  obtain ⟨⟨v, hv, hR⟩, hp⟩ := hm
  refine Writes.mono (hstep i hi m' hfr ⟨v, hv, hR⟩ hp)
    (Fp.inBlock_le_inBlock (by omega) (by omega)) fun m'' hfr' ⟨⟨x, hx, hRx⟩, hp'⟩ => ?_
  have hv' := hfr'.keep (Store.readsOnly_holdsVec b o i v)
    (fun _ _ h₁ h₂ => by obtain ⟨-, h₁, -⟩ := h₁; obtain ⟨-, -, h₂⟩ := h₂; omega) hv
  refine ⟨⟨fun j => if j = i then x else v j, fun j hj => ?_, fun j hj => ?_⟩, hp'⟩
  · rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · dsimp only; rw [if_neg (by omega)]; exact hv' j hj
    · dsimp only; rw [if_pos rfl]; exact hx
  · rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · dsimp only; rw [if_neg (by omega)]; exact hR j hj
    · dsimp only; rw [if_pos rfl]; exact hRx

/-- **The two loops that fill a matrix with values known only by a relation**, by columns in the
layout `L` (a matrix stored by rows is the layout of its transpose). -/
theorem writes_fillRel₂ [Nonempty K] {n₁ n₂ : IExp} {body : Stmt Op Tst} (L : MatLayout)
    (hL : L.Valid) (hn₁ : n₁.eval ρ.idx = some L.cols)
    (hn₂ : ∀ j, n₂.eval (ρ.pushIdx j).idx = some L.rows)
    (R : ℕ → ℕ → K → Prop) (pos : ℕ → ℕ) (hpos : m.pos = pos 0)
    (hstep : ∀ j < L.cols, ∀ i < L.rows, ∀ m', m.store.EqOff (L.upto j i) m'.store →
      (∃ A : ℕ → ℕ → K, m'.store.HoldsMatUpto L A j i ∧
        (∀ i' < L.rows, ∀ j' < j, R i' j' (A i' j')) ∧ ∀ i' < i, R i' j (A i' j)) →
      m'.pos = pos (j * L.rows + i) →
      Writes md I τ body ((ρ.pushIdx j).pushIdx i) (Store.inBlock L.buf (L.cell i j) 1)
        (fun m'' => (∃ x, m''.store.get L.buf (L.cell i j) = some x ∧ R i j x) ∧
          m''.pos = pos (j * L.rows + i + 1)) m') :
    Writes md I τ (.loop n₁ (.loop n₂ body)) ρ L.fp
      (fun m' => (∃ A : ℕ → ℕ → K, m'.store.HoldsMat L A ∧
        ∀ i < L.rows, ∀ j < L.cols, R i j (A i j)) ∧ m'.pos = pos (L.cols * L.rows)) m := by
  have h := writes_loop₂ (P := fun j i m' => (∃ A : ℕ → ℕ → K, m'.store.HoldsMatUpto L A j i ∧
        (∀ i' < L.rows, ∀ j' < j, R i' j' (A i' j')) ∧ ∀ i' < i, R i' j (A i' j)) ∧
      m'.pos = pos (j * L.rows + i)) hn₁ hn₂ (fun j i => L.upto j i)
    (fun j _ i _ => by rw [MatLayout.upto_succ]; exact le_sup_left)
    (fun j _ => by rw [MatLayout.upto_col])
    ⟨⟨fun _ _ => Classical.arbitrary K, ⟨fun _ _ _ h => absurd h (Nat.not_lt_zero _),
      fun _ h => absurd h (Nat.not_lt_zero _)⟩, fun _ _ _ h => absurd h (Nat.not_lt_zero _),
      fun _ h => absurd h (Nat.not_lt_zero _)⟩, by simpa using hpos⟩
    (fun j _ m' ⟨⟨A, hA, hR₁, hR₂⟩, hp⟩ => ⟨⟨A, ⟨fun i' hi' j' hj' => by
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj' with hj' | rfl
        · exact hA.1 i' hi' j' hj'
        · exact hA.2 i' hi', fun _ h => absurd h (Nat.not_lt_zero _)⟩, fun i' hi' j' hj' => by
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj' with hj' | rfl
        · exact hR₁ i' hi' j' hj'
        · exact hR₂ i' hi', fun _ h => absurd h (Nat.not_lt_zero _)⟩,
      by rw [hp, Nat.succ_mul, Nat.add_zero]⟩)
    fun j hj i hi m' hfr hm => Writes.mono (hstep j hj i hi m' hfr hm.1 hm.2)
      (by rw [MatLayout.upto_succ]; exact le_sup_right) fun m'' hfr' hm' => ?_
  · rw [MatLayout.upto_cols] at h
    exact Writes.mono h le_rfl fun _ _ ⟨⟨A, hA, hR, _⟩, hp⟩ =>
      ⟨⟨A, Store.holdsMatUpto_cols.mp hA, hR⟩, by rw [hp, Nat.add_zero]⟩
  obtain ⟨⟨A, hA, hR₁, hR₂⟩, -⟩ := hm
  obtain ⟨⟨x, hx, hRx⟩, hp'⟩ := hm'
  have hold : ∀ i' j', (j' < j ∧ i' < L.rows) ∨ (j' = j ∧ i' < i) →
      m''.store.get L.buf (L.cell i' j') = m'.store.get L.buf (L.cell i' j') := by
    intro i' j' hc
    refine hfr'.get_eq fun hin => ?_
    obtain ⟨-, h1, h2⟩ := hin
    unfold MatLayout.Valid at hL
    simp only [MatLayout.cell] at h1 h2
    rcases hc with ⟨hj', hi'⟩ | ⟨rfl, hi'⟩
    · have := Nat.mul_le_mul_right L.ld (show j' + 1 ≤ j by omega)
      rw [Nat.succ_mul] at this
      omega
    · omega
  refine ⟨⟨fun i' j' => if j' = j ∧ i' = i then x else A i' j', ⟨fun i' hi' j' hj' => ?_,
    fun i' hi' => ?_⟩, fun i' hi' j' hj' => ?_, fun i' hi' => ?_⟩, hp'⟩
  · dsimp only; rw [if_neg (by omega), hold i' j' (Or.inl ⟨hj', hi'⟩)]; exact hA.1 i' hi' j' hj'
  · rcases Nat.lt_succ_iff_lt_or_eq.mp hi' with hi' | rfl
    · dsimp only; rw [if_neg (by omega), hold i' j (Or.inr ⟨rfl, hi'⟩)]; exact hA.2 i' hi'
    · dsimp only; rw [if_pos ⟨rfl, rfl⟩]; exact hx
  · dsimp only; rw [if_neg (by omega)]; exact hR₁ i' hi' j' hj'
  · rcases Nat.lt_succ_iff_lt_or_eq.mp hi' with hi' | rfl
    · dsimp only; rw [if_neg (by omega)]; exact hR₂ i' hi'
    · dsimp only; rw [if_pos ⟨rfl, rfl⟩]; exact hRx

/-- **The loop with early exit**, in the standard invariant form. At a round below the cap the
test is evaluated (its Boolean is known from the access model: `IsCmp`, `holds_testAt`): if it
holds the body keeps the invariant, otherwise the continuation runs with the round index. At the
cap the continuation runs without a test. The footprint is that of the rounds and of the
continuation. -/
theorem writes_whileFuel {fuel : IExp} {q : Tst} {ds : List IExp} {ins : List Operand}
    {body k : Stmt Op Tst} {N : ℕ} (hn : fuel.eval ρ.idx = some N) (F : ℕ → Fp)
    (hF : ∀ i < N, F i ≤ F (i + 1)) (G : Fp) (Inv : ℕ → Mem K → Prop) (P : Mem K → Prop)
    (h0 : Inv 0 m)
    (hstep : ∀ i < N, ∀ m', m.store.EqOff (F i) m'.store → Inv i m' →
      md.Holds (I.testAt q ds ins (ρ.pushIdx i) m') fun c =>
        if c then Writes md I τ body (ρ.pushIdx i) (F (i + 1)) (Inv (i + 1)) m'
        else Writes md I τ k (ρ.pushIdx i) G P m')
    (hcap : ∀ m', m.store.EqOff (F N) m'.store → Inv N m' →
      Writes md I τ k (ρ.pushIdx N) G P m') :
    Writes md I τ (.whileFuel fuel q ds ins body k) ρ (F N ⊔ G) P m := by
  have hle := Fp.le_of_chain hF
  refine wp_whileFuel hn (fun i m' => m.store.EqOff (F i) m'.store ∧ Inv i m')
    ⟨Store.EqOff.refl _ _, h0⟩ (fun i hi m' hm => (hstep i hi m' hm.1 hm.2).mono fun c hc => ?_)
    fun m' hm => Wp.mono (hcap m' hm.1 hm.2) fun _ hm' => ⟨hm.1.trans' hm'.1, hm'.2⟩
  cases c with
  | true => exact Wp.mono hc fun _ hm' => ⟨(hm.1.mono (hF i hi)).trans hm'.1, hm'.2⟩
  | false =>
    exact Wp.mono hc fun _ hm' => ⟨(hm.1.trans' hm'.1).mono fun b j h =>
      h.elim (fun h => Or.inl (hle i N (by omega) le_rfl b j h)) Or.inr, hm'.2⟩

/-- **The strict loop** (`Stmt.whileStrict`): the loop with early exit that fails if the test
still holds after the fuel. `nidx` is the number of index variables in scope. At the round `N`
(the fuel) the test must fail (only for success: in liberal mode a run that reaches it fails). -/
theorem writes_whileStrict {nidx : ℕ} {fuel : IExp} {q : Tst} {ds : List IExp}
    {ins : List Operand} {body : Stmt Op Tst} {N : ℕ} (hn : fuel.eval ρ.idx = some N)
    (hnidx : ρ.idx.length = nidx) (F : ℕ → Fp) (hF : ∀ i < N, F i ≤ F (i + 1))
    (Inv : ℕ → Mem K → Prop) (P : Mem K → Prop) (h0 : Inv 0 m)
    (hstep : ∀ i < N, ∀ m', m.store.EqOff (F i) m'.store → Inv i m' →
      md.Holds (I.testAt q ds ins (ρ.pushIdx i) m') fun c =>
        if c then Writes md I τ body (ρ.pushIdx i) (F (i + 1)) (Inv (i + 1)) m' else P m')
    (hcap : ∀ m', m.store.EqOff (F N) m'.store → Inv N m' →
      md.Holds (I.testAt q ds ins (ρ.pushIdx N) m') fun c =>
        md.Needs (c = false) ∧ (c = false → P m')) :
    Writes md I τ (Stmt.whileStrict nidx fuel q ds ins body) ρ (F N) P m := by
  have hN1 : (fuel + IExp.const 1).eval ρ.idx = some (N + 1) := by simp [hn]
  have hz : ∀ i, (fuel - IExp.var nidx).eval (ρ.pushIdx i).idx = some (N - i) := by
    intro i
    simp [IExp.eval_append hn, ← hnidx]
  have hmin : min (N + 1) N = N := by omega
  refine Writes.mono (writes_whileFuel hN1 (fun i => F (min i N)) (fun i hi => ?_) ⊥
      (fun i m' => i ≤ N ∧ Inv i m') P ⟨Nat.zero_le _, h0⟩
      (fun i hi m' hfr hm => ?_) fun m' _ hm => absurd hm.1 (by omega))
    (fun b j h => h.elim (fun h => by rwa [hmin] at h) False.elim) fun _ _ h => h
  · rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [min_eq_left (by omega), min_eq_left (by omega)]
      exact hF i hi
    · rw [min_self, hmin]
  · obtain ⟨hiN, hinv⟩ := hm
    rcases Nat.lt_or_eq_of_le hiN with hlt | rfl
    · rw [min_eq_left hiN] at hfr
      refine (hstep i hlt m' hfr hinv).mono fun c hc => ?_
      cases c with
      | true =>
        exact wp_seq (wp_ifZero (hz i) (by
          rw [if_neg (by omega)]
          exact Wp.mono hc fun m'' hm'' =>
            ⟨by rw [min_eq_left (show i + 1 ≤ N by omega)]; exact hm''.1, by omega, hm''.2⟩))
      | false => exact Writes.skip hc
    · rw [min_self] at hfr
      refine (hcap m' hfr hinv).mono fun c hc => ?_
      cases c with
      | true =>
        cases md with
        | total => exact absurd (hc.1 rfl) (by decide)
        | liberal =>
          rw [if_pos rfl]
          unfold Writes
          refine wp_seq (wp_ifZero (hz i) ?_)
          rw [if_pos (by simp)]
          exact wp_abort_liberal
      | false => exact Writes.skip (hc.2 rfl)

/-- A branch on a size being positive. -/
theorem writes_ifPos {e : IExp} {body : Stmt Op Tst} {n : ℕ} {F : Fp} {P : Mem K → Prop}
    (he : e.eval ρ.idx = some n)
    (h : if 0 < n then Writes md I τ body (ρ.pushIdx 0) F P m else P m) :
    Writes md I τ (.ifPos e body) ρ F P m := by
  refine wp_ifPos he ?_
  split_ifs at h ⊢ with hn
  · exact h
  · exact ⟨Store.EqOff.refl _ _, h⟩

/-- A branch on a size being zero. -/
theorem writes_ifZero {e : IExp} {body : Stmt Op Tst} {n : ℕ} {F : Fp} {P : Mem K → Prop}
    (he : e.eval ρ.idx = some n)
    (h : if n = 0 then Writes md I τ body (ρ.pushIdx 0) F P m else P m) :
    Writes md I τ (.ifZero e body) ρ F P m := by
  refine wp_ifZero he ?_
  split_ifs at h ⊢ with hn
  · exact h
  · exact ⟨Store.EqOff.refl _ _, h⟩

end NLAlib.Ops
