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

**Phase A**: statements only (`sorry`).
-/

@[expose] public section

namespace NLAlib.Ops

variable {Op Tst K : Type} {md : Mode} {I : Interp Op Tst K} {τ : Tape K} {ρ : Env}
  {m : Mem K}

/-- **The counted loop**, in the standard invariant form. -/
theorem writes_loop {n : IExp} {body : Stmt Op Tst} {N : ℕ} (hn : n.eval ρ.idx = some N)
    (F : ℕ → Fp) (hF : ∀ i < N, F i ≤ F (i + 1)) (P : ℕ → Mem K → Prop) (h0 : P 0 m)
    (hstep : ∀ i < N, ∀ m', m.store.EqOff (F i) m'.store → P i m' →
      Writes md I τ body (ρ.pushIdx i) (F (i + 1)) (P (i + 1)) m') :
    Writes md I τ (.loop n body) ρ (F N) (P N) m := by sorry

/-- **Two nested counted loops**, with an invariant indexed by the row `i` and the column `j`;
the end of a row is the start of the next (`hnext`). -/
theorem writes_loop₂ {n₁ n₂ : IExp} {body : Stmt Op Tst} {M N : ℕ}
    (hn₁ : n₁.eval ρ.idx = some M) (hn₂ : ∀ i, n₂.eval (ρ.pushIdx i).idx = some N)
    (F : ℕ → ℕ → Fp) (hF : ∀ i < M, ∀ j < N, F i j ≤ F i (j + 1))
    (hrow : ∀ i < M, F i N ≤ F (i + 1) 0) (P : ℕ → ℕ → Mem K → Prop) (h0 : P 0 0 m)
    (hnext : ∀ i < M, ∀ m', P i N m' → P (i + 1) 0 m')
    (hstep : ∀ i < M, ∀ j < N, ∀ m', m.store.EqOff (F i j) m'.store → P i j m' →
      Writes md I τ body ((ρ.pushIdx i).pushIdx j) (F i (j + 1)) (P i (j + 1)) m') :
    Writes md I τ (.loop n₁ (.loop n₂ body)) ρ (F M 0) (P M 0) m := by sorry

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
      (fun m' => m'.store.HoldsVec b o N v ∧ m'.pos = pos N) m := by sorry

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
      (fun m' => m'.store.HoldsMat L A ∧ m'.pos = pos (L.cols * L.rows)) m := by sorry

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
        m'.pos = pos N) m := by sorry

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
  sorry

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
    Writes md I τ (.whileFuel fuel q ds ins body k) ρ (F N ⊔ G) P m := by sorry

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
    Writes md I τ (Stmt.whileStrict nidx fuel q ds ins body) ρ (F N) P m := by sorry

/-- A branch on a size being positive. -/
theorem writes_ifPos {e : IExp} {body : Stmt Op Tst} {n : ℕ} {F : Fp} {P : Mem K → Prop}
    (he : e.eval ρ.idx = some n)
    (h : if 0 < n then Writes md I τ body (ρ.pushIdx 0) F P m else P m) :
    Writes md I τ (.ifPos e body) ρ F P m := by sorry

/-- A branch on a size being zero. -/
theorem writes_ifZero {e : IExp} {body : Stmt Op Tst} {n : ℕ} {F : Fp} {P : Mem K → Prop}
    (he : e.eval ρ.idx = some n)
    (h : if n = 0 then Writes md I τ body (ρ.pushIdx 0) F P m else P m) :
    Writes md I τ (.ifZero e body) ρ F P m := by sorry

end NLAlib.Ops
