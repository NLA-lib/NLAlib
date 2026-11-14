/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.Orthogonalization.CGS2.Extend
public import NLAlib.Krylov.Lanczos.Reorth.SweepInterface

/-!
# One column of the column-wise two-pass Gram–Schmidt extension

The round of `NLAlib.CGS2.cgs2Extend` for one column of the block, as a block specification
that serves the exact and the rounded analysis: the words written and the cells preserved are
the same in both, and only the relations of the norm and of the scaling differ, so these two
relations are parameters. The round reads the stored basis followed by the new columns already
written as one block, and returns the words of both passes, of the two norms and of the branch
taken by the deflation test.

## Main definitions

* `NLAlib.CGS2.nrm2RelOf`, `NLAlib.CGS2.scalRelOf`: the contracts of the norm and of the scaling
  for an arbitrary relation.
* `NLAlib.CGS2.ColOps`: the contracts of the operations called by a round.
* `NLAlib.CGS2.cgs2ExtendFinish`, `NLAlib.CGS2.cgs2ExtendColumn`: the deflation test with its
  branches, and the round.
* `NLAlib.CGS2.colEnv`, `NLAlib.CGS2.colFp`, `NLAlib.CGS2.ColMem`: the environment, the
  footprint and the layout of a round.
* `NLAlib.CGS2.ColOut`: the words computed by a round and their relations.

## Main results

* `NLAlib.CGS2.cgs2Extend_eq`: the program is two allocations around the loop of the rounds.
* `NLAlib.CGS2.ColMem.of_eqOff`: the layout is kept by a frame.
* `NLAlib.CGS2.writes_zeroRows`, `NLAlib.CGS2.writes_zeroCol`, `NLAlib.CGS2.writes_addRows`: the
  three inner loops.
* `NLAlib.CGS2.writes_finish`: the deflation test and its branches.
* `NLAlib.CGS2.exists_readBlock_column`, `NLAlib.CGS2.exists_colOut`: the coefficient column
  read back.
* `NLAlib.CGS2.writes_column`: one round.
-/

@[expose] public section

namespace NLAlib.CGS2

open Ops Krylov.Lanczos.Reorth

variable {K Op Tst : Type} [Inhabited K]

/-- The contract of `nrm2` for an arbitrary relation `N` between the length, the block read and
the word written: one block of length `n` to one cell. -/
@[simps (attr := storeNF)]
def nrm2RelOf (N : ℕ → (ℕ → K) → K → Prop) : BlockRel K where
  nd := 1
  inLens d := [d.headD 0]
  outLens _ := [1]
  rel d X _ ys := match X, ys with
    | [xs], [[v]] => N (d.headD 0) (vec xs) v
    | _, _ => False

/-- The contract of `scal` for an arbitrary relation `S` between the length, the divisor, the
block read and the block written: a cell and a block of length `n` to the block. -/
@[simps (attr := storeNF)]
def scalRelOf (S : ℕ → K → (ℕ → K) → (ℕ → K) → Prop) : BlockRel K where
  nd := 1
  inLens d := [1, d.headD 0]
  outLens d := [d.headD 0]
  rel d X _ ys := match X, ys with
    | [[a], xs], [zs] => S (d.headD 0) a (vec xs) (vec zs)
    | _, _ => False

variable [Has ScalarOp Op] [Has Blas1Op Op] [Has CmpTst Tst]

/-- **The contracts of the operations called by one round** of the column-wise extension:
functional scalar arithmetic on the machine `M`, dot products and updates with the errors
`ed`, `ea`, exact negation, a norm with the relation `N`, a scaling with the relation `S`, an
exact copy, and exact comparisons; the level-1 operations at the lengths `ok`. -/
structure ColOps (M : Machine K) (dec : K → ℝ) (ed : ℕ → ℝ) (ea : ℝ)
    (N : ℕ → (ℕ → K) → K → Prop) (S : ℕ → K → (ℕ → K) → (ℕ → K) → Prop) (ok : ℕ → Prop)
    (I : Interp Op Tst K) : Prop where
  /-- Scalar arithmetic is the machine `M`. -/
  scalar : IsScalar M I
  /-- `dot`. -/
  dot : I.Meets .total (Has.inj Blas1Op.dot) ((dotRel dec ed).spec (OutApart ok))
  /-- `axpy`. -/
  axpy : I.Meets .total (Has.inj Blas1Op.axpy) ((axpyRel dec ea).spec (InPlace ok))
  /-- Negation is exact. -/
  neg : ∀ a, dec (M.neg a) = -dec a
  /-- `nrm2`, with the relation `N`. -/
  nrm2 : I.Meets .total (Has.inj Blas1Op.nrm2) ((nrm2RelOf N).spec (OutApart ok))
  /-- `scal`, with the relation `S`. -/
  scal : I.Meets .total (Has.inj Blas1Op.scal) ((scalRelOf S).spec (InPlace ok))
  /-- `copy`. -/
  copy : I.Meets .total (Has.inj Blas1Op.copy) ((copyRel (K := K)).spec (OutApart ok))
  /-- The comparisons. -/
  cmp : IsCmp dec I

/-- The offset of column `c` of the block `W`. -/
local notation "eW" => (IExp.var 4 + IExp.var 8 * IExp.var 0)
/-- The offset of column `c` of the coefficient block. -/
local notation "eC" => (IExp.var 7 + IExp.var 8 * (IExp.var 1 + IExp.var 2))
/-- The offset of column `c` of the new block. -/
local notation "eQ" => (IExp.var 5 + IExp.var 8 * IExp.var 0)

omit [Inhabited K] in
/-- **The deflation test of a round and its branches**: the norm of the reduced column in the
second scalar cell, the rounded product of the threshold literal and the saved norm in the
third, and the comparison; the new column is set to zero, or it is the reduced column divided
by its norm and the norm is the diagonal coefficient. -/
def cgs2ExtendFinish (τ : ℚ) : Stmt Op Tst :=
  (Stmt.call (Has.inj Blas1Op.nrm2) [IExp.var 0] [⟨1, eW⟩] [⟨6, IExp.const 1⟩]).seq
    ((Stmt.call (Has.inj (ScalarOp.lit τ)) [] [] [⟨6, IExp.const 2⟩]).seq
      ((Stmt.call (Has.inj ScalarOp.mul) [] [⟨6, IExp.const 2⟩, ⟨6, IExp.const 0⟩]
          [⟨6, IExp.const 2⟩]).seq
        (Stmt.ite (Has.inj CmpTst.le) [] [⟨6, IExp.const 1⟩, ⟨6, IExp.const 2⟩]
          (Stmt.loop (IExp.var 0)
            (Stmt.call (Has.inj (ScalarOp.lit 0)) [] [] [⟨2, eQ + IExp.var 9⟩]))
          ((Stmt.call (Has.inj Blas1Op.copy) [IExp.var 0] [⟨1, eW⟩] [⟨2, eQ⟩]).seq
            ((Stmt.call (Has.inj Blas1Op.scal) [IExp.var 0] [⟨6, IExp.const 1⟩, ⟨2, eQ⟩]
                [⟨2, eQ⟩]).seq
              (Stmt.call (Has.inj ScalarOp.copy) [] [⟨6, IExp.const 1⟩]
                [⟨4, eC + IExp.var 1 + IExp.var 8⟩]))))))

omit [Inhabited K] in
/-- **The round of column `c`** of `NLAlib.CGS2.cgs2Extend`: the saved norm, the zero rows of
the coefficient column, the two classical passes, the sum of their coefficients, and the
deflation test with its branches. -/
def cgs2ExtendColumn (τ : ℚ) : Stmt Op Tst :=
  (Stmt.call (Has.inj Blas1Op.nrm2) [IExp.var 0] [⟨1, eW⟩] [⟨6, IExp.const 0⟩]).seq
    ((Stmt.loop (IExp.var 2)
        (Stmt.call (Has.inj (ScalarOp.lit 0)) [] [] [⟨4, eC + IExp.var 1 + IExp.var 9⟩])).seq
      ((Stmt.frame [IExp.var 0, IExp.var 1 + IExp.var 8]
          [⟨0, IExp.var 3⟩, ⟨1, eW⟩, ⟨1, eW⟩, ⟨4, eC⟩] cgsPass).seq
        ((Stmt.frame [IExp.var 0, IExp.var 1 + IExp.var 8]
            [⟨0, IExp.var 3⟩, ⟨1, eW⟩, ⟨1, eW⟩, ⟨5, IExp.const 0⟩] cgsPass).seq
          ((Stmt.loop (IExp.var 1 + IExp.var 8)
              (Stmt.call (Has.inj ScalarOp.add) [] [⟨4, eC + IExp.var 9⟩, ⟨5, IExp.var 9⟩]
                [⟨4, eC + IExp.var 9⟩])).seq
            (cgs2ExtendFinish τ)))))

omit [Inhabited K] in
/-- The program is the loop of the rounds inside its two allocations. -/
theorem cgs2Extend_eq (τ : ℚ) : cgs2Extend (Op := Op) (Tst := Tst) τ =
    Stmt.alloc (IExp.var 1 + IExp.var 2)
      (Stmt.alloc (IExp.const 3) (Stmt.loop (IExp.var 2) (cgs2ExtendColumn τ))) := rfl

/-- The environment of round `c`: the dimensions `[n, k, b]`, the five operands (the new block
is the end of the basis), the two scratch handles `hb`, `tb` and the column index. -/
abbrev colEnv (n k b c : ℕ) (Q W C : ℕ × ℕ) (hb tb : ℕ) : Env :=
  (((Env.frame [n, k, b] [Q, W, (Q.1, Q.2 + k * n), W, C]).pushBuf hb).pushBuf tb).pushIdx c

/-- The cells written by round `c`: column `c` of the block, of the coefficients and of the new
block, and the two scratch buffers. -/
abbrev colFp (n k b c : ℕ) (Q W C : ℕ × ℕ) (hb tb : ℕ) : Fp :=
  Store.inBlock W.1 (W.2 + c * n) n ⊔ Store.inBlock C.1 (C.2 + c * (k + b)) (k + b) ⊔
    Store.inBlock Q.1 (Q.2 + k * n + c * n) n ⊔ Store.inBuf hb ⊔ Store.inBuf tb

/-- **The layout of the rounds** at a memory `m`: the buffers of the basis `Q`, the block `W`
and the coefficients `C` are distinct and below the scratch handles `hb < tb`, which are live,
and there is room for the `k + b` columns of the basis buffer, the `b` columns of the block,
the `(k + b) × b` coefficients, `k + b` scratch coefficients and three scratch scalars. -/
structure ColMem (n k b : ℕ) (Q W C : ℕ × ℕ) (hb tb : ℕ) (m : Mem K) : Prop where
  /-- The basis and the block are in two buffers. -/
  hQW : Q.1 ≠ W.1
  /-- The basis and the coefficients are in two buffers. -/
  hQC : Q.1 ≠ C.1
  /-- The block and the coefficients are in two buffers. -/
  hWC : W.1 ≠ C.1
  /-- The basis is below the scratch. -/
  hQh : Q.1 < hb
  /-- The block is below the scratch. -/
  hWh : W.1 < hb
  /-- The coefficients are below the scratch. -/
  hCh : C.1 < hb
  /-- The coefficient scratch is below the scalar scratch. -/
  hht : hb < tb
  /-- The scalar scratch is live. -/
  live : tb < m.store.length
  /-- Room for the basis and the new block. -/
  roomQ : Q.2 + k * n + b * n ≤ m.store.len Q.1
  /-- Room for the block. -/
  roomW : W.2 + b * n ≤ m.store.len W.1
  /-- Room for the coefficients. -/
  roomC : C.2 + (k + b) * b ≤ m.store.len C.1
  /-- Room for the coefficients of a pass. -/
  roomh : k + b ≤ m.store.len hb
  /-- Room for three scalars. -/
  roomt : 3 ≤ m.store.len tb

omit [Has ScalarOp Op] [Has Blas1Op Op] [Has CmpTst Tst] [Inhabited K] in
/-- The layout of the rounds is kept by a frame: a frame keeps the lengths. -/
theorem ColMem.of_eqOff {n k b : ℕ} {Q W C : ℕ × ℕ} {hb tb : ℕ} {m m' : Mem K}
    (h : ColMem n k b Q W C hb tb m) {F : Fp} (hfr : m.store.EqOff F m'.store) :
    ColMem n k b Q W C hb tb m' :=
  ⟨h.hQW, h.hQC, h.hWC, h.hQh, h.hWh, h.hCh, h.hht, by rw [hfr.length_eq]; exact h.live,
    by rw [hfr.len_eq]; exact h.roomQ, by rw [hfr.len_eq]; exact h.roomW,
    by rw [hfr.len_eq]; exact h.roomC, by rw [hfr.len_eq]; exact h.roomh,
    by rw [hfr.len_eq]; exact h.roomt⟩

omit [Inhabited K] [Has Blas1Op Op] [Has CmpTst Tst] in
/-- The loop that sets the rows `k, …, k + b - 1` of column `c` of the coefficient block to the
zero literal writes those cells only. -/
theorem writes_zeroRows {M : Machine K} {I : Interp Op Tst K} (hS : IsScalar M I) {τ' : Tape K}
    {n k b c : ℕ} {Q W C : ℕ × ℕ} {hb tb : ℕ} {m : Mem K} (hC : C.1 < m.store.length)
    (hroom : C.2 + c * (k + b) + k + b ≤ m.store.len C.1) :
    Writes .total I τ' (Stmt.loop (IExp.var 2)
        (Stmt.call (Has.inj (ScalarOp.lit 0)) [] [] [⟨4, eC + IExp.var 1 + IExp.var 9⟩]))
      (colEnv n k b c Q W C hb tb) (Store.inBlock C.1 (C.2 + c * (k + b) + k) b)
      (fun m' => m'.store.HoldsVec C.1 (C.2 + c * (k + b) + k) b (fun _ => M.lit 0) ∧
        m'.pos = m.pos) m := by
  refine writes_fill (b := C.1) (o := C.2 + c * (k + b) + k) rfl (fun _ => M.lit 0)
    (fun _ => m.pos) rfl fun i hi m' hfr hv hpos => ?_
  step (hS (.lit 0)) as m₂ hfr₂ ⟨hpos₂, z, hz, hzw⟩
  exact ⟨hzw ▸ hz, hpos₂.trans hpos⟩

omit [Inhabited K] [Has Blas1Op Op] [Has CmpTst Tst] in
/-- The loop that sets column `c` of the new block to the zero literal writes that column
only. -/
theorem writes_zeroCol {M : Machine K} {I : Interp Op Tst K} (hS : IsScalar M I) {τ' : Tape K}
    {n k b c : ℕ} {Q W C : ℕ × ℕ} {hb tb : ℕ} {m : Mem K} (hQ : Q.1 < m.store.length)
    (hroom : Q.2 + k * n + c * n + n ≤ m.store.len Q.1) :
    Writes .total I τ' (Stmt.loop (IExp.var 0)
        (Stmt.call (Has.inj (ScalarOp.lit 0)) [] [] [⟨2, eQ + IExp.var 9⟩]))
      (colEnv n k b c Q W C hb tb) (Store.inBlock Q.1 (Q.2 + k * n + c * n) n)
      (fun m' => m'.store.HoldsVec Q.1 (Q.2 + k * n + c * n) n (fun _ => M.lit 0) ∧
        m'.pos = m.pos) m := by
  refine writes_fill (b := Q.1) (o := Q.2 + k * n + c * n) rfl (fun _ => M.lit 0)
    (fun _ => m.pos) rfl fun i hi m' hfr hv hpos => ?_
  step (hS (.lit 0)) as m₂ hfr₂ ⟨hpos₂, z, hz, hzw⟩
  exact ⟨hzw ▸ hz, hpos₂.trans hpos⟩

omit [Has Blas1Op Op] [Has CmpTst Tst] in
/-- The loop that adds the coefficients `h₂` of the second pass, in the scratch, to the
coefficients `h₁` of the first, in column `c` of the coefficient block: the first `k + c` rows
of that column then hold the machine sums, and nothing else is written. -/
theorem writes_addRows {M : Machine K} {I : Interp Op Tst K} (hS : IsScalar M I) {τ' : Tape K}
    {n k b c : ℕ} {Q W C : ℕ × ℕ} {hb tb : ℕ} {m : Mem K} {h₁ h₂ : List K}
    (hC : C.1 < m.store.length) (hh : hb < m.store.length) (hCh : C.1 < hb)
    (hroom : C.2 + c * (k + b) + (k + c) ≤ m.store.len C.1)
    (h1 : m.store.readBlock C.1 (C.2 + c * (k + b)) (k + c) = some h₁)
    (h2 : m.store.readBlock hb 0 (k + c) = some h₂) :
    Writes .total I τ' (Stmt.loop (IExp.var 1 + IExp.var 8)
        (Stmt.call (Has.inj ScalarOp.add) [] [⟨4, eC + IExp.var 9⟩, ⟨5, IExp.var 9⟩]
          [⟨4, eC + IExp.var 9⟩]))
      (colEnv n k b c Q W C hb tb) (Store.inBlock C.1 (C.2 + c * (k + b)) (k + c))
      (fun m' => m'.store.HoldsVec C.1 (C.2 + c * (k + b)) (k + c)
          (fun i => M.add (vec h₁ i) (vec h₂ i)) ∧ m'.pos = m.pos) m := by
  refine writes_fill (b := C.1) (o := C.2 + c * (k + b)) rfl
    (fun i => M.add (vec h₁ i) (vec h₂ i)) (fun _ => m.pos) rfl fun i hi m' hfr hv hpos => ?_
  have hx := Store.get_of_readBlock h1 hi default
  have hy := Store.get_of_readBlock h2 hi default
  rw [Nat.zero_add] at hy
  step (hS .add) as m₂ hfr₂ ⟨hpos₂, z, hz, hzw⟩
  exact ⟨hzw ▸ hz, hpos₂.trans hpos⟩

/-- The deflation test of a round. From a memory whose first scalar cell holds the saved
norm `ν₀` and whose column `c` of the block holds the reduced column `w₂`, the test computes a
norm `β` of `w₂` and writes column `c` of the new block: if `β` is at most the machine product
of the threshold literal and `ν₀`, the column is zero and the diagonal coefficient is not
written; otherwise the column is `w₂` scaled by `β` and the diagonal coefficient is `β`. -/
theorem writes_finish {M : Machine K} {dec : K → ℝ} {ed : ℕ → ℝ} {ea : ℝ}
    {N : ℕ → (ℕ → K) → K → Prop} {S : ℕ → K → (ℕ → K) → (ℕ → K) → Prop} {ok : ℕ → Prop}
    {I : Interp Op Tst K} (ops : ColOps M dec ed ea N S ok I) {τ' : Tape K} {τ : ℚ}
    {n k b c : ℕ} {Q W C : ℕ × ℕ} {hb tb : ℕ} {m : Mem K} {ν₀ : K} {w₂ : List K}
    (L : ColMem n k b Q W C hb tb m) (hc : c < b) (hok : ok n)
    (hν : m.store.get tb 0 = some ν₀)
    (hw : m.store.readBlock W.1 (W.2 + c * n) n = some w₂) :
    Writes .total I τ' (cgs2ExtendFinish τ) (colEnv n k b c Q W C hb tb)
      (Store.inBlock Q.1 (Q.2 + k * n + c * n) n ⊔
        Store.inBlock C.1 (C.2 + c * (k + b) + k + c) 1 ⊔ Store.inBuf tb)
      (fun m' => m'.pos = m.pos ∧ ∃ β qc, N n (vec w₂) β ∧
        m'.store.readBlock Q.1 (Q.2 + k * n + c * n) n = some qc ∧
        ((dec β ≤ dec (M.mul (M.lit τ) ν₀) ∧ (∀ i < n, vec qc i = M.lit 0) ∧
            m'.store.get C.1 (C.2 + c * (k + b) + k + c) =
              m.store.get C.1 (C.2 + c * (k + b) + k + c)) ∨
          (¬ dec β ≤ dec (M.mul (M.lit τ) ν₀) ∧ S n β (vec w₂) (vec qc) ∧
            m'.store.get C.1 (C.2 + c * (k + b) + k + c) = some β))) m := by
  classical
  obtain ⟨hQW, hQC, hWC, hQh, hWh, hCh, hht, hlive, hrQ, hrW, hrC, hrh, hrt⟩ := id L
  have hcn : c * n + n ≤ b * n := by
    have h := Nat.mul_le_mul_right n (Nat.succ_le_of_lt hc)
    rwa [Nat.succ_mul] at h
  have hck : c * (k + b) + (k + b) ≤ (k + b) * b := by
    have h := Nat.mul_le_mul_right (k + b) (Nat.succ_le_of_lt hc)
    rwa [Nat.succ_mul, Nat.mul_comm b] at h
  have hWQ : W.1 ≠ Q.1 := hQW.symm
  have hWt : W.1 ≠ tb := by omega
  have htQ : tb ≠ Q.1 := by omega
  have htC : tb ≠ C.1 := by omega
  have hQl : Q.1 < m.store.length := by omega
  have hWl : W.1 < m.store.length := by omega
  have hCl : C.1 < m.store.length := by omega
  unfold cgs2ExtendFinish
  step ops.nrm2 as m₁ hfr₁ ⟨hpos₁, β, hβ, hnβ⟩
  step (ops.scalar (.lit τ)) as m₂ hfr₂ ⟨hpos₂, t, ht, htw⟩
  step (ops.scalar .mul) as m₃ hfr₃ ⟨hpos₃, tt, htt, httw⟩
  have hβ₃ : m₃.store.get tb 1 = some β := by kept
  refine writes_ite rfl rfl (ops.cmp.test_le (x := (tb, 1)) (y := (tb, 2)) hβ₃ htt) ?_
  subst htw httw
  by_cases hle : dec β ≤ dec (M.mul (M.lit τ) ν₀)
  · simp only [hle, decide_true, ite_true]
    refine (writes_zeroCol ops.scalar (m := m₃) (by room) (by room)).mono (by fp_sub) ?_
    intro m₄ hfr₄ ⟨hq, hpos₄⟩
    refine ⟨by simp [hpos₄, hpos₃, hpos₂, hpos₁], β, _, hnβ,
      Store.holdsVec_iff_readBlock.mp hq, Or.inl ⟨hle, fun i hi => vec_map_range _ hi, ?_⟩⟩
    rw [hfr₄.get_eq (by disjoint), hfr₃.get_eq (by disjoint), hfr₂.get_eq (by disjoint),
      hfr₁.get_eq (by disjoint)]
  · simp only [hle, decide_false, Bool.false_eq_true, ite_false]
    step ops.copy as m₄ hfr₄ ⟨hpos₄, copied, hcopied, hcopy⟩
    subst copied
    step ops.scal as m₅ hfr₅ ⟨hpos₅, qc, hqc, hscal⟩
    step (ops.scalar .copy) as m₆ hfr₆ ⟨hpos₆, z, hz, hzw⟩
    subst hzw
    exact ⟨by simp [hpos₆, hpos₅, hpos₄, hpos₃, hpos₂, hpos₁], β, qc, hnβ, by kept,
      Or.inr ⟨hle, hscal, hz⟩⟩

/-- **The words computed by one round and their relations**, for `j` stored columns `vs` of
length `n`, the input column `wc`, the reduced column `w₂`, the coefficient column `cc` of `r`
rows and the new column `qc`: there are a saved norm `ν₀` of `wc`, two classical passes from
`wc` to `mid` and from `mid` to `w₂` with coefficients `h₁`, `h₂`, and a norm `β` of `w₂`, such
that the first `j` rows of `cc` are the machine sums of `h₁` and `h₂`, the rows after `j` are
the zero literal, and either `β` is at most the machine product of the threshold literal and
`ν₀`, row `j` of `cc` is the zero literal and `qc` is the zero literal, or `β` is larger, row
`j` of `cc` is `β` and `qc` is `w₂` scaled by `β`. -/
def ColOut (M : Machine K) (dec : K → ℝ) (ed ea : ℝ) (N : (ℕ → K) → K → Prop)
    (S : K → (ℕ → K) → (ℕ → K) → Prop) (τ : ℚ) (n j r : ℕ) (vs wc w₂ cc qc : List K) : Prop :=
  ∃ (ν₀ β : K) (mid h₁ h₂ : List K), N (vec wc) ν₀ ∧ PassOut dec ed ea n j vs wc mid h₁ ∧
    PassOut dec ed ea n j vs mid w₂ h₂ ∧ N (vec w₂) β ∧
    (∀ i < j, vec cc i = M.add (vec h₁ i) (vec h₂ i)) ∧
    (∀ i, j < i → i < r → vec cc i = M.lit 0) ∧
    ((dec β ≤ dec (M.mul (M.lit τ) ν₀) ∧ vec cc j = M.lit 0 ∧ ∀ i < n, vec qc i = M.lit 0) ∨
      (¬ dec β ≤ dec (M.mul (M.lit τ) ν₀) ∧ vec cc j = β ∧ S β (vec w₂) (vec qc)))

omit [Has ScalarOp Op] [Has Blas1Op Op] [Has CmpTst Tst] in
/-- A block of `r` cells whose first `j` cells hold `a`, whose cell `j` holds `d` and whose
later cells hold `z` is read back as a list with those entries. -/
theorem exists_readBlock_column {s : Store K} {bC o j r : ℕ} {a : ℕ → K} {d z : K}
    (hjr : j < r) (ha : ∀ i < j, s.get bC (o + i) = some (a i))
    (hd : s.get bC (o + j) = some d) (hz : ∀ i, j < i → i < r → s.get bC (o + i) = some z) :
    ∃ cc, s.readBlock bC o r = some cc ∧ (∀ i < j, vec cc i = a i) ∧ vec cc j = d ∧
      ∀ i, j < i → i < r → vec cc i = z := by
  refine ⟨(List.range r).map fun i => if i < j then a i else if i = j then d else z,
    Store.holdsVec_iff_readBlock.mp fun i hi => ?_, fun i hi => ?_, ?_, fun i hji hi => ?_⟩
  · show s.get bC (o + i) = some (if i < j then a i else if i = j then d else z)
    rcases lt_trichotomy i j with h | rfl | h
    · rw [if_pos h]
      exact ha i h
    · rw [if_neg (lt_irrefl _), if_pos rfl]
      exact hd
    · rw [if_neg (by omega), if_neg (by omega)]
      exact hz i h hi
  · rw [vec_map_range _ (by omega), if_pos hi]
  · rw [vec_map_range _ hjr, if_neg (lt_irrefl _), if_pos rfl]
  · rw [vec_map_range _ hi, if_neg (by omega), if_neg (by omega)]

omit [Has ScalarOp Op] [Has Blas1Op Op] [Has CmpTst Tst] in
/-- The coefficient column of a round after the deflation test: the sums written before the
test and the zero rows are kept by the frame of the test, and the diagonal coefficient is the
zero literal or the norm according to the branch, so the column is read back with the relations
of `NLAlib.CGS2.ColOut`. -/
theorem exists_colOut {M : Machine K} {dec : K → ℝ} {ed ea : ℝ} {N : (ℕ → K) → K → Prop}
    {S : K → (ℕ → K) → (ℕ → K) → Prop} {τ : ℚ} {n k b c : ℕ} {Q C : ℕ × ℕ} {tb : ℕ}
    {m₅ m₆ : Mem K} {ν₀ β : K} {vs wc mid w₂ h₁ h₂ qc : List K}
    (hfr : m₅.store.EqOff (Store.inBlock Q.1 (Q.2 + k * n + c * n) n ⊔
      Store.inBlock C.1 (C.2 + c * (k + b) + k + c) 1 ⊔ Store.inBuf tb) m₆.store)
    (hc : c < b) (hQC : Q.1 ≠ C.1) (hCt : C.1 ≠ tb) (hn₀ : N (vec wc) ν₀)
    (hp₁ : PassOut dec ed ea n (k + c) vs wc mid h₁)
    (hp₂ : PassOut dec ed ea n (k + c) vs mid w₂ h₂) (hnβ : N (vec w₂) β)
    (hs : m₅.store.HoldsVec C.1 (C.2 + c * (k + b)) (k + c)
      fun i => M.add (vec h₁ i) (vec h₂ i))
    (hz : ∀ r, c ≤ r → r < b →
      m₅.store.get C.1 (C.2 + c * (k + b) + k + r) = some (M.lit 0))
    (hbr : (dec β ≤ dec (M.mul (M.lit τ) ν₀) ∧ (∀ i < n, vec qc i = M.lit 0) ∧
        m₆.store.get C.1 (C.2 + c * (k + b) + k + c) =
          m₅.store.get C.1 (C.2 + c * (k + b) + k + c)) ∨
      (¬ dec β ≤ dec (M.mul (M.lit τ) ν₀) ∧ S β (vec w₂) (vec qc) ∧
        m₆.store.get C.1 (C.2 + c * (k + b) + k + c) = some β)) :
    ∃ cc, m₆.store.readBlock C.1 (C.2 + c * (k + b)) (k + b) = some cc ∧
      ColOut M dec ed ea N S τ n (k + c) (k + b) vs wc w₂ cc qc := by
  have hCQ : C.1 ≠ Q.1 := hQC.symm
  have htC : tb ≠ C.1 := hCt.symm
  have ha : ∀ i < k + c, m₆.store.get C.1 (C.2 + c * (k + b) + i) =
      some (M.add (vec h₁ i) (vec h₂ i)) :=
    fun i hi => (hfr.get_eq (by disjoint)).trans (hs i hi)
  have hzr : ∀ i, k + c < i → i < k + b →
      m₆.store.get C.1 (C.2 + c * (k + b) + i) = some (M.lit 0) := by
    intro i h1 h2
    have h0 := hz (i - k) (by omega) (by omega)
    rw [show C.2 + c * (k + b) + k + (i - k) = C.2 + c * (k + b) + i by omega] at h0
    exact (hfr.get_eq (by disjoint)).trans h0
  have hd : ∃ d, m₆.store.get C.1 (C.2 + c * (k + b) + (k + c)) = some d ∧
      ((dec β ≤ dec (M.mul (M.lit τ) ν₀) ∧ d = M.lit 0 ∧ ∀ i < n, vec qc i = M.lit 0) ∨
        (¬ dec β ≤ dec (M.mul (M.lit τ) ν₀) ∧ d = β ∧ S β (vec w₂) (vec qc))) := by
    rw [← Nat.add_assoc]
    rcases hbr with ⟨hle, hq, hC⟩ | ⟨hle, hsc, hC⟩
    · exact ⟨M.lit 0, hC.trans (hz c le_rfl hc), Or.inl ⟨hle, rfl, hq⟩⟩
    · exact ⟨β, hC, Or.inr ⟨hle, rfl, hsc⟩⟩
  obtain ⟨d, hd, hbr'⟩ := hd
  obtain ⟨cc, hcc, hadd, hdiag, hzero⟩ := exists_readBlock_column (by omega) ha hd hzr
  refine ⟨cc, hcc, ν₀, β, mid, h₁, h₂, hn₀, hp₁, hp₂, hnβ, hadd, hzero, ?_⟩
  rw [hdiag]
  exact hbr'

/-- One round of the column-wise extension. From a memory with the layout of the rounds in
which the `k + c` stored columns (the basis followed by the new columns before `c`) are read as
one block `vs` and column `c` of the block is `wc`, the round writes only column `c` of the
block, of the coefficients and of the new block and the scratch, keeps the position, and the
three columns written satisfy `NLAlib.CGS2.ColOut`. -/
theorem writes_column {M : Machine K} {dec : K → ℝ} {ed : ℕ → ℝ} {ea : ℝ}
    {N : ℕ → (ℕ → K) → K → Prop} {S : ℕ → K → (ℕ → K) → (ℕ → K) → Prop} {ok : ℕ → Prop}
    {I : Interp Op Tst K} (ops : ColOps M dec ed ea N S ok I) {τ' : Tape K} {τ : ℚ}
    {n k b c : ℕ} {Q W C : ℕ × ℕ} {hb tb : ℕ} {m : Mem K} {vs wc : List K}
    (L : ColMem n k b Q W C hb tb m) (hc : c < b) (hok : ok n)
    (hV : m.store.readBlock Q.1 Q.2 ((k + c) * n) = some vs)
    (hw : m.store.readBlock W.1 (W.2 + c * n) n = some wc) :
    Writes .total I τ' (cgs2ExtendColumn τ) (colEnv n k b c Q W C hb tb)
      (colFp n k b c Q W C hb tb)
      (fun m' => m'.pos = m.pos ∧ ∃ w₂ cc qc,
        m'.store.readBlock W.1 (W.2 + c * n) n = some w₂ ∧
        m'.store.readBlock C.1 (C.2 + c * (k + b)) (k + b) = some cc ∧
        m'.store.readBlock Q.1 (Q.2 + k * n + c * n) n = some qc ∧
        ColOut M dec (ed n) ea (N n) (S n) τ n (k + c) (k + b) vs wc w₂ cc qc) m := by
  obtain ⟨hQW, hQC, hWC, hQh, hWh, hCh, hht, hlive, hrQ, hrW, hrC, hrh, hrt⟩ := id L
  have hcn : c * n + n ≤ b * n := by
    have h := Nat.mul_le_mul_right n (Nat.succ_le_of_lt hc)
    rwa [Nat.succ_mul] at h
  have hck : c * (k + b) + (k + b) ≤ (k + b) * b := by
    have h := Nat.mul_le_mul_right (k + b) (Nat.succ_le_of_lt hc)
    rwa [Nat.succ_mul, Nat.mul_comm b] at h
  have hWt : W.1 ≠ tb := by omega
  have hQl : Q.1 < m.store.length := by omega
  have hWl : W.1 < m.store.length := by omega
  have hCl : C.1 < m.store.length := by omega
  have hhl : hb < m.store.length := by omega
  unfold cgs2ExtendColumn
  step ops.nrm2 as m₁ hfr₁ ⟨hpos₁, ν₀, hν₀, hn₀⟩
  refine Writes.seq_le (writes_zeroRows ops.scalar (m := m₁) (by room) (by room)) (by fp_sub)
    fun m₂ hfr₂ ⟨hz₂, hpos₂⟩ => ?_
  have hl₂ : m₂.Live [Q, (W.1, W.2 + c * n), (C.1, C.2 + c * (k + b))] := by room
  have hV₂ : m₂.store.readBlock Q.1 Q.2 ((k + c) * n) = some vs := by kept
  have hw₂ : m₂.store.readBlock W.1 (W.2 + c * n) n = some wc := by kept
  refine Writes.seq_le (writes_frame rfl rfl (by room)
    (cgsPass_writes (Q := Q) (w := (W.1, W.2 + c * n)) (H := (C.1, C.2 + c * (k + b)))
      ops.scalar ops.dot ops.axpy ops.neg hok hQW hQC hWC hl₂ hV₂ hw₂
      ⟨by room, by room, trivial⟩)) (by fp_sub)
    fun m₃ hfr₃ ⟨hpos₃, mid, h₁, hmid, hh₁, hp₁⟩ => ?_
  have hh₁' : m₃.store.readBlock C.1 (C.2 + c * (k + b)) (k + c) = some h₁ := hh₁
  have hmid' : m₃.store.readBlock W.1 (W.2 + c * n) n = some mid := hmid
  have hl₃ : m₃.Live [Q, (W.1, W.2 + c * n), (hb, 0)] := by room
  have hV₃ : m₃.store.readBlock Q.1 Q.2 ((k + c) * n) = some vs := by kept
  refine Writes.seq_le (writes_frame rfl rfl (by room)
    (cgsPass_writes (Q := Q) (w := (W.1, W.2 + c * n)) (H := (hb, 0))
      ops.scalar ops.dot ops.axpy ops.neg hok hQW (Nat.ne_of_lt hQh) (Nat.ne_of_lt hWh) hl₃ hV₃
      hmid' ⟨by room, by room, trivial⟩)) (by fp_sub)
    fun m₄ hfr₄ ⟨hpos₄, w₂, h₂, hw₂', hh₂, hp₂⟩ => ?_
  have hw₄ : m₄.store.readBlock W.1 (W.2 + c * n) n = some w₂ := hw₂'
  have hh₁₄ : m₄.store.readBlock C.1 (C.2 + c * (k + b)) (k + c) = some h₁ := by kept
  have hh₂' : m₄.store.readBlock hb 0 (k + c) = some h₂ := hh₂
  refine Writes.seq_le (writes_addRows ops.scalar (m := m₄) (by room) (by room) hCh (by room)
    hh₁₄ hh₂') (by fp_sub) fun m₅ hfr₅ ⟨hs₅, hpos₅⟩ => ?_
  have hν₅ : m₅.store.get tb 0 = some ν₀ := by kept
  have hw₅ : m₅.store.readBlock W.1 (W.2 + c * n) n = some w₂ := by kept
  have hz₅ : ∀ r, c ≤ r → r < b →
      m₅.store.get C.1 (C.2 + c * (k + b) + k + r) = some (M.lit 0) := by
    intro r hcr hr
    have h0 : m₂.store.get C.1 (C.2 + c * (k + b) + k + r) = some (M.lit 0) := hz₂ r hr
    kept
  have L₅ := ((((L.of_eqOff hfr₁).of_eqOff hfr₂).of_eqOff hfr₃).of_eqOff hfr₄).of_eqOff hfr₅
  refine (writes_finish ops L₅ hc hok hν₅ hw₅).mono (by fp_sub)
    fun m₆ hfr₆ ⟨hpos₆, β, qc, hnβ, hqc, hbr⟩ => ?_
  obtain ⟨cc, hcc, hout⟩ := exists_colOut hfr₆ hc hQC (by omega) hn₀ hp₁ hp₂ hnβ hs₅ hz₅ hbr
  exact ⟨by rw [hpos₆, hpos₅, hpos₄, hpos₃, hpos₂, hpos₁], w₂, cc, qc, by kept, hcc, hqc, hout⟩

end NLAlib.CGS2
