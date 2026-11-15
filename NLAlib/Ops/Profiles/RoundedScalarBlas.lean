/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Profiles.RoundedBlas
public import NLAlib.Ops.Blas.DotFunction
public import NLAlib.Ops.Logic.Writes

/-!
# Sequential rounded BLAS over scalar-only primitives

The fixed lowering expands vector operations and sequential summation, then removes the unused
vector names. Its target signature is exactly scalar arithmetic. The unused-name erasure is
proved independent of its arbitrary values: no fallback vector meaning survives in the tree.
The numerical contracts are inherited from the existing sequential BLAS certificate.

## Main results

* `NLAlib.Ops.RoundedScalarBlas.table`: a computable scalar-only lowering.
* `NLAlib.Ops.RoundedScalarBlas.table_independent`: unused vector erasures do not affect it.
* `NLAlib.Ops.RoundedScalarBlas.model`: unit-weight scalar arithmetic with exact comparisons.
* `NLAlib.Ops.RoundedScalarBlas.contracts_link`: derive rounded vector contracts from scalars.
-/

@[expose] public section

namespace NLAlib.Ops.RoundedScalarBlas

variable {Tst : Type}

/-- Rename scalar calls; supply an arbitrary erasure for vector names that have already
been expanded. Independence of that erasure is proved for the complete table below. -/
def erase (unused : Blas1Op → ScalarOp) : Table RCLikeBlas.Operation ScalarOp Tst
  | .inl o => .inr o
  | .inr o => .inr (unused o)

/-- Expand level-one calls and their sequential summation, then retain only scalar names.
Both expansion stages use the existing proved implementation tables. -/
def tableWith (unused : Blas1Op → ScalarOp) : Table RCLikeBlas.Operation ScalarOp Tst :=
  (Blas.level1Table (Op := RCLikeBlas.Operation)).comp Blas.sumSeqTable |>.comp (erase unused)

/-- All vector calls have been expanded before erasure: arbitrary values for leftover vector
names give definitionally identical final scalar trees. -/
theorem table_independent (f g : Blas1Op → ScalarOp) :
    (tableWith f : Table RCLikeBlas.Operation ScalarOp Tst) = tableWith g := by
  funext o
  cases o with
  | inl a => rfl
  | inr a => cases a <;> rfl

/-- The complete fixed implementation has scalar operations as its entire target signature. -/
def table : Table RCLikeBlas.Operation ScalarOp Tst := tableWith (fun _ => .copy)

/-- The scalar-only tree derives all rounded level-one laws from the scalar machine alone.
No vector primitive meaning or whole-program execution fact is requested. -/
theorem laws {K : Type} [Inhabited K] {M : Machine K} {dec : K → ℝ} {u : ℝ}
    (hM : StdModel u dec M) (hu : 0 ≤ u) {I : Interp ScalarOp Tst K}
    (hI : IsScalar M I) :
    IsScalar M (I.link table) ∧ IsBlas1 dec (Blas.seq.err u) (fun _ => True) (I.link table) := by
  have hS : IsScalar M (I.link (erase (Tst := Tst) (fun _ => .copy))) := by
    intro o
    exact Interp.link_meets_kept rfl (hI o)
  have h := (Blas.seq_certifies (Op := RCLikeBlas.Operation) hM hu
    (fun _ => True)).meets _ hS
  simpa only [Interp.link_comp, table, tableWith, Blas.seq, Profile.over,
    Blas.level1, Blas.sumSeq] using h

/-- Recomputing a dot product on identical input words returns the same word, even after
other state changes. This derives functionality from the actual scalar implementation. -/
theorem isFn_dot {K : Type} [Inhabited K] {M : Machine K} {I : Interp ScalarOp Tst K}
    (hI : IsScalar M I) :
    (I.link table).IsFn .total (Has.inj Blas1Op.dot) (dotSeqFn M)
      (OutApart (fun _ => True)) := by
  have hS : IsScalar M (I.link (erase (Tst := Tst) (fun _ => .copy))) := by
    intro o
    exact Interp.link_meets_kept rfl (hI o)
  have h := isFn_dot_seq hS
  simpa only [Interp.link_comp, table, tableWith, Blas.seq, Profile.over,
    Blas.level1, Blas.sumSeq] using h

/-- Exact scalar arithmetic gives the exact level-one contracts of the actual lowered trees. -/
theorem exact_laws {K : Type} [Inhabited K] {M : Machine K} {dec : K → ℝ}
    (hM : ExactModel dec M) {I : Interp ScalarOp Tst K} (hI : IsScalar M I) :
    IsExactBlas1 dec (fun _ => True) (I.link table) := by
  have hsum : Blas.seqSumErr 0 = fun _ => 0 := by
    funext n
    simp [Blas.seqSumErr]
  apply IsBlas1.toExact
  simpa [Blas.seq.err, Blas.level1Err, hsum] using
    (laws hM.toStdModel_zero le_rfl hI).2

/-- The existing sequential norm lowering, renamed into any scalar-operation signature.
Its entire syntax consists of scalar calls, loops and scoped scratch allocation. -/
def nrm2 {Op : Type} [Has ScalarOp Op] : Impl Op Tst :=
  ⟨1, 1, 1, ((.call (Has.inj Blas1Op.nrm2) [.var 0] [⟨0, .var 1⟩] [⟨1, .var 2⟩] :
    Stmt RCLikeBlas.Operation Tst).link table).link (fun o => .inr (Has.inj o))⟩

/-- The actual scalar-lowered sequential norm computes the exact nonnegative Euclidean norm
of its supplied real words. Only scalar contracts, exact arithmetic, input reads and output
capacity are assumed; no vector operation remains primitive. -/
theorem writes_nrm2_exact {Op : Type} [Has ScalarOp Op] {M : Machine ℝ}
    {I : Interp Op Tst ℝ} (hS : IsScalar M I) (hE : ExactModel id M)
    {τ : Tape ℝ} {m : Mem ℝ} {n : ℕ} {x z : ℕ × ℕ} {xs : List ℝ}
    (hl : m.Live [x, z]) (hx : m.store.readBlock x.1 x.2 n = some xs)
    (hz : z.2 < m.store.len z.1) (hxz : x.1 ≠ z.1) :
    Writes .total I τ nrm2.body (Env.frame [n] [x, z]) (Store.inBlock z.1 z.2 1)
      (fun μ => μ.pos = m.pos ∧ μ.store.get z.1 z.2 =
        some (Real.sqrt (∑ i ∈ Finset.range n, (vec xs i) ^ 2))) m := by
  let rename : Table ScalarOp Op Tst := fun o => .inr (Has.inj o)
  let J := I.link rename
  have hJ : IsScalar M J := fun o => Interp.link_meets_kept rfl (hS o)
  have hB := exact_laws hE hJ
  have hw := writes_call_cell (τ := τ) (m := m) (I := J.link table) hB.nrm2
    (ρ := Env.frame [n] [x, z]) (d := [n]) (a := [x]) (z := z) (k := 0)
    (ds := [.var 0]) (ins := [⟨0, .var 1⟩]) (outs := [⟨1, .var 2⟩])
    rfl rfl rfl rfl rfl rfl (by simpa [OutApart] using hxz)
    (fun _ => ⟨hl, ⟨[xs], by simp [Mem.readBlocks, nrm2ExactRel, nrm2Rel, hx], trivial⟩, hz⟩)
  have hread : m.readBlocks [x] [n] = some [xs] := by simp [Mem.readBlocks, hx]
  have hw' := hw.mono (P' := fun μ => μ.pos = m.pos ∧ μ.store.get z.1 z.2 =
    some (Real.sqrt (∑ i ∈ Finset.range n, (vec xs i) ^ 2))) le_rfl (fun μ _ hp => ?_)
  · change Writes .total I τ _ _ _ _ m
    simpa only [Writes, Wp, nrm2, run_link, J, rename] using hw'
  · obtain ⟨hpos, vals, value, hvals, hvalue, hrel⟩ := hp
    have he : vals = [xs] := Option.some.inj (hvals.symm.trans hread)
    subst vals
    have hv : value = Real.sqrt (∑ i ∈ Finset.range n, (vec xs i) ^ 2) := by
      simpa [nrm2ExactRel] using hrel
    exact ⟨by simpa using hpos, hv ▸ hvalue⟩

/-- Unit-work scalar cells with no hidden primitive workspace. Canonical control, addressing,
allocation and comparison costs remain the shared nonzero charges. -/
def resources : ResourceModel ScalarOp CmpTst :=
  Functional.cellResources (fun o => Standard.signature (.scalar o))
    (fun _ _ => 1) (fun _ _ => 0)

/-- A closed model with only the supplied scalar machine functions and exact operand
comparisons. Its signature contains neither vector nor matrix primitives. -/
noncomputable def model {r b : ℕ} (P : Problem ℝ r b) (M : Machine ℝ) :
    AccessModel ScalarOp CmpTst P :=
  Functional.model P id (fun _ _ => M.fn) resources

/-- Model contracts supply exactly the scalar machine functions and operand comparisons. -/
theorem model_laws {r b : ℕ} {P : Problem ℝ r b} {M : Machine ℝ}
    {d : Fin r → ℕ} {x : P.Input d} {I : Interp ScalarOp CmpTst ℝ}
    (h : (model P M).contracts d x I) : IsScalar M I ∧ IsCmp id I :=
  ⟨fun o => Functional.isFn h o, Functional.isCmp h⟩

/-- Every interpreter of the scalar-only model induces the declared rounded BLAS model
through the actual scalar implementation, with no remaining vector primitive assumption. -/
theorem contracts_link {r b : ℕ} {P : Problem ℝ r b} {M : Machine ℝ} {u : ℝ}
    (hM : StdModel u id M) (hu : 0 ≤ u) {cost : Standard.Costing}
    {d : Fin r → ℕ} {x : P.Input d} {I : Interp ScalarOp CmpTst ℝ}
    (h : (model P M).contracts d x I) :
    (RoundedBlas.model P M u hM hu cost).contracts d x (I.link table) := by
  obtain ⟨hS, hB⟩ := laws hM hu (model_laws h).1
  refine ⟨?_, h.2⟩
  intro o
  cases o with
  | inl a => exact hS a
  | inr a => cases a with
    | sum => exact hB.sum
    | dot => exact hB.dot
    | axpy => exact hB.axpy
    | nrm2 => exact hB.nrm2
    | scal => exact hB.scal
    | copy => exact hB.copy

end NLAlib.Ops.RoundedScalarBlas
