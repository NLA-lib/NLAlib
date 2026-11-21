/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Profiles.RoundedBlas
public import NLAlib.Ops.Blas.DotFunction
public import NLAlib.Ops.Logic.Writes
public import NLAlib.Ops.RoutineSyntax
public import NLAlib.Ops.Logic.RoutineIntro

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
* `NLAlib.Ops.RoundedScalarBlas.nrm2_meets`, `NLAlib.Ops.RoundedScalarBlas.nrm2_meets_stdModel`,
  `NLAlib.Ops.RoundedScalarBlas.nrm2_meets_word`: the judgments of the norm under exact
  arithmetic, under the standard model (two-sided) and on any machine. The statements
  `nrm2_writes_exact`, `nrm2_writes_stdModel` and `nrm2_writes` are their readings at one cell.
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
    exact Interp.link_satisfies_kept rfl (hI o)
  have h := (Blas.seq_certifies (Op := RCLikeBlas.Operation) hM hu
    (fun _ => True)).satisfies _ hS
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
    exact Interp.link_satisfies_kept rfl (hI o)
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

/-- The sequential Euclidean norm over scalar operations, `[n] (x : n) → (z : 1)`: the call of
`nrm2` linked through the scalar table and renamed into any scalar-operation signature. Its
whole tree consists of scalar calls, loops and scoped scratch allocation. -/
def nrm2 {Op : Type} [Has ScalarOp Op] : Routine Op Tst :=
  routine% [n] (x : n) → (z : 1) :=
    ((.call (Has.inj Blas1Op.nrm2) [.var 0] [⟨0, .var 1⟩] [⟨1, .var 2⟩] :
      Stmt RCLikeBlas.Operation Tst).link table).link (fun o => .inr (Has.inj o))

/-- The run of the tree of the norm is the linked call of `nrm2`: at any contract `R` of that
call in the shape of the norm, the tree writes one cell related to the block read. The step
shared by the judgments of the norm, one for each machine model. -/
private theorem nrm2_writes_rel {Op : Type} [Has ScalarOp Op] {I : Interp Op Tst ℝ}
    {R : BlockRel ℝ}
    (hR : ((I.link (fun o => .inr (Has.inj o) : Table ScalarOp Op Tst)).link table).Satisfies
      .total (Has.inj Blas1Op.nrm2) (R.spec (OutApart fun _ => True)))
    {τ : Tape ℝ} {m : Mem ℝ} {n : ℕ} {x z : ℕ × ℕ} {xs : List ℝ}
    (hnd : [n].length = R.nd) (hwin : R.win [n] = 0) (hout : R.outLens [n] = [1])
    (hin : R.inLens [n] = [n]) (hdom : R.dom [n] [xs] (τ.window R.stream m.pos 0))
    (hl : m.Live [x, z]) (hx : m.store.readBlock x.1 x.2 n = some xs)
    (hz : z.2 < m.store.len z.1) (hxz : x.1 ≠ z.1) :
    Writes .total I τ nrm2.body (Env.frame [n] [x, z]) (Store.inBlock z.1 z.2 1)
      (fun μ => μ.pos = m.pos ∧ ∃ v : ℝ, μ.store.get z.1 z.2 = some v ∧
        R.rel [n] [xs] (τ.window R.stream m.pos 0) [[v]]) m := by
  have hread : m.readBlocks [x] (R.inLens [n]) = some [xs] := by
    simp [hin, Mem.readBlocks, hx]
  have hw := writes_call_cell (τ := τ) (m := m) hR
    (ρ := Env.frame [n] [x, z]) (d := [n]) (a := [x]) (z := z) (k := 0)
    (ds := [.var 0]) (ins := [⟨0, .var 1⟩]) (outs := [⟨1, .var 2⟩])
    rfl rfl rfl hnd hwin hout (by simpa [OutApart] using hxz)
    (fun _ => ⟨hl, ⟨[xs], hread, hdom⟩, hz⟩)
  have hw' := hw.mono (P' := fun μ => μ.pos = m.pos ∧ ∃ v : ℝ, μ.store.get z.1 z.2 = some v ∧
    R.rel [n] [xs] (τ.window R.stream m.pos 0) [[v]]) le_rfl (fun μ _ hp => ?_)
  · change Writes .total I τ _ _ _ _ m
    simpa only [Writes, Wp, nrm2, run_link] using hw'
  · obtain ⟨hpos, vals, value, hvals, hvalue, hrel⟩ := hp
    obtain rfl : vals = [xs] := Option.some.inj (hvals.symm.trans hread)
    exact ⟨by simpa using hpos, value, hvalue, hrel⟩

/-- The scalar renaming of a scalar interpretation keeps the scalar contracts. -/
private theorem isScalar_rename {Op : Type} [Has ScalarOp Op] {M : Machine ℝ}
    {I : Interp Op Tst ℝ} (hS : IsScalar M I) :
    IsScalar M (I.link (fun o => .inr (Has.inj o) : Table ScalarOp Op Tst)) :=
  fun o => Interp.link_satisfies_kept rfl (hS o)

/-- The sequential Euclidean norm meets its specification under exact scalar arithmetic: the
written cell is the Euclidean norm of the block read. Only scalar contracts and exact
arithmetic are assumed; no vector operation remains primitive. -/
theorem nrm2_meets {Op : Type} [Has ScalarOp Op] {M : Machine ℝ} {I : Interp Op Tst ℝ}
    (hS : IsScalar M I) (hE : ExactModel id M) :
    (nrm2 (Op := Op) (Tst := Tst)).Meets I
      (spec% [n] (xs) → ([v]) ensures v = Real.sqrt (∑ i ∈ Finset.range n, (vec xs i) ^ 2)) := by
  routine_intro [n] (x, z) reads (xs)
  refine (nrm2_writes_rel (exact_laws hE (isScalar_rename hS)).nrm2 rfl rfl rfl rfl trivial
    (by simp [Mem.Live, hl.1, hl.2]) hxs (by omega) hxz).mono (by fp_sub) ?_
  rintro μ - ⟨hpos, v, hget, hrel⟩
  have hv : v = Real.sqrt (∑ i ∈ Finset.range n, (vec xs i) ^ 2) := by
    simpa [nrm2ExactRel] using hrel
  exact ⟨by simpa using hpos, [[v]],
    Mem.readBlocks_of_cons (Store.readBlock_one_of_get hget) rfl, hv⟩

/-- The judgment `NLAlib.Ops.RoundedScalarBlas.nrm2_meets` read at one cell: under exact
arithmetic the run stores the Euclidean norm of the words read. A corollary kept in operand
form because its caller frames the tree inside a stage whose contract states the stored cell
(`NLAlib.ShiftedQR.matrixNorm`), not a reported block. -/
theorem nrm2_writes_exact {Op : Type} [Has ScalarOp Op] {M : Machine ℝ}
    {I : Interp Op Tst ℝ} (hS : IsScalar M I) (hE : ExactModel id M)
    {τ : Tape ℝ} {m : Mem ℝ} {n : ℕ} {x z : ℕ × ℕ} {xs : List ℝ}
    (hl : m.Live [x, z]) (hx : m.store.readBlock x.1 x.2 n = some xs)
    (hz : z.2 < m.store.len z.1) (hxz : x.1 ≠ z.1) :
    Writes .total I τ nrm2.body (Env.frame [n] [x, z]) (Store.inBlock z.1 z.2 1)
      (fun μ => μ.pos = m.pos ∧ μ.store.get z.1 z.2 =
        some (Real.sqrt (∑ i ∈ Finset.range n, (vec xs i) ^ 2))) m := by
  have h := nrm2_meets (Tst := Tst) hS hE [n] [x, z] τ m [xs] rfl rfl hl (by routine_sep)
    (Mem.readBlocks_of_cons hx rfl) trivial (by routine_nf; simpa [Mem.Room] using hz)
  refine h.mono (by routine_nf; fp_sub) ?_
  rintro μ - ⟨hpos, ys, hys, hpost⟩
  routine_nf at hys
  obtain ⟨z', zs, hz', hzs, rfl⟩ := Mem.readBlocks_one hys
  obtain rfl : z = z' := by simpa using hz'
  obtain ⟨v, rfl⟩ := List.length_eq_one_iff.mp (Store.readBlock_eq_some_iff.mp hzs).1
  obtain rfl : v = Real.sqrt (∑ i ∈ Finset.range n, (vec xs i) ^ 2) := hpost
  exact ⟨hpos, by simpa using Store.get_of_readBlock hzs (j := 0) Nat.one_pos 0⟩

/-- The numbers of the rounded norm: a sum of squares $\sigma$ within $E S$ of $S \ge 0$, with
$E \le nu + (nu)^2$ when $S > 0$, and a square root $\nu$ within $u\sqrt{\sigma}$ of
$\sqrt{\sigma}$ give $\lvert \nu - \sqrt S\rvert \le (n + 2)u\sqrt S$ when $(n + 2)u \le 1/2$:
the square root halves the relative error of the sum, up to the factor $2/3$. -/
private theorem nrm2_bounds {u S σ ν E : ℝ} {n : ℕ} (hu : 0 ≤ u) (hnu : ((n : ℝ) + 2) * u ≤ 1 / 2)
    (hS : 0 ≤ S) (hE : 0 < S → E ≤ n * u + (n * u) ^ 2) (hσ : |σ - S| ≤ E * S)
    (hν : 0 ≤ σ → |ν - √σ| ≤ u * √σ) :
    (1 - ((n : ℝ) + 2) * u) * √S ≤ ν ∧ ν ≤ (1 + ((n : ℝ) + 2) * u) * √S := by
  rcases hS.eq_or_lt with hS0 | hSp
  · subst hS0
    have hσ0 : σ = 0 := by simpa using hσ
    subst hσ0
    have := hν le_rfl
    simp only [Real.sqrt_zero, mul_zero, sub_zero, abs_nonpos_iff] at this
    simp [this]
  have hx : (0 : ℝ) ≤ n * u := by positivity
  have hx2 : (n : ℝ) * u ≤ 1 / 2 - 2 * u := by linarith
  have hE' := hE hSp
  have hE0 : 0 ≤ E := by
    by_contra h; push Not at h; nlinarith [abs_nonneg (σ - S)]
  have hE34 : E ≤ 3 / 4 := by nlinarith
  obtain ⟨hσl, hσu⟩ := abs_le.mp hσ
  have hσ4 : S / 4 ≤ σ := by nlinarith
  have hσ0 : 0 ≤ σ := by linarith
  set a := √S with ha
  set b := √σ with hb
  have ha2 : a ^ 2 = S := Real.sq_sqrt hS
  have hb2 : b ^ 2 = σ := Real.sq_sqrt hσ0
  have ha0 : 0 < a := Real.sqrt_pos.mpr hSp
  have hb0 : 0 ≤ b := Real.sqrt_nonneg σ
  have hba : a / 2 ≤ b := by nlinarith
  have hdiff : |b - a| ≤ 2 / 3 * E * a := by
    rw [abs_le]
    constructor <;> nlinarith [mul_nonneg hE0 ha0.le]
  obtain ⟨hνl, hνu⟩ := abs_le.mp (hν hσ0)
  obtain ⟨hdl, hdu⟩ := abs_le.mp hdiff
  have hkey : u + 2 / 3 * E * (1 + u) ≤ ((n : ℝ) + 2) * u := by
    nlinarith [mul_nonneg hu hx, mul_nonneg (mul_nonneg hu hu) hx, mul_nonneg hu hE0]
  constructor <;> nlinarith [mul_nonneg hu ha0.le, mul_nonneg (mul_nonneg hu hE0) ha0.le]

/-- **The rounded scalar-lowered norm is two-sided accurate**: under the standard model at
$\boldsymbol{u}$ with $(n + 2)\boldsymbol{u} \le 1/2$, the stored $x$ of the sequential norm of $n$
real words $x_0, \dots, x_{n-1}$ satisfies
$(1 - (n + 2)\boldsymbol{u})\sqrt{\sum_i x_i^2} \le x \le (1 + (n + 2)\boldsymbol{u})
\sqrt{\sum_i x_i^2}$: the $n$ squares and the $n$ sequential additions of nonnegative terms
([Higham2002, §3.1]) and the rounded square root. In particular $x = 0$ exactly when every word
is $0$. -/
theorem nrm2_meets_stdModel {Op : Type} [Has ScalarOp Op] {M : Machine ℝ} {u : ℝ}
    {I : Interp Op Tst ℝ} (hS : IsScalar M I) (hM : StdModel u id M) :
    (nrm2 (Op := Op) (Tst := Tst)).Meets I
      (spec% [n] (xs) → ([v]) requires ((n : ℝ) + 2) * u ≤ 1 / 2 ensures
        (1 - ((n : ℝ) + 2) * u) * Real.sqrt (∑ i ∈ Finset.range n, (vec xs i) ^ 2) ≤ v ∧
        v ≤ (1 + ((n : ℝ) + 2) * u) * Real.sqrt (∑ i ∈ Finset.range n, (vec xs i) ^ 2)) := by
  routine_intro [n] (x, z) reads (xs)
  have hu : ((n : ℝ) + 2) * u ≤ 1 / 2 := hpre
  have hu0 : 0 ≤ u := by simpa using (abs_nonneg _).trans (hM.lit 1)
  refine (nrm2_writes_rel (laws hM hu0 (isScalar_rename hS)).2.nrm2 rfl rfl rfl rfl trivial
    (by simp [Mem.Live, hl.1, hl.2]) hxs (by omega) hxz).mono (by fp_sub) ?_
  rintro μ - ⟨hpos, v, hget, hrel⟩
  obtain ⟨σ, hσ, hν⟩ : IsNrm2Err id ((Blas.seq.err u).dot n) (Blas.seq.err u).sqrt n (vec xs)
      v := by
    simpa [nrm2Rel] using hrel
  refine ⟨by simpa using hpos, [[v]],
    Mem.readBlocks_of_cons (Store.readBlock_one_of_get hget) rfl,
    nrm2_bounds (E := (Blas.seq.err u).dot n) hu0 hu
      (Finset.sum_nonneg fun i _ => sq_nonneg _) ?_ ?_ hν⟩
  · intro hSp
    have hn : n ≠ 0 := by rintro rfl; simp at hSp
    have hdot : (Blas.seq.err u).dot n = (1 + u) ^ n - 1 := by
      simp only [Blas.seq.err, Blas.level1Err, Blas.seqSumErr]
      obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
      simp only [Nat.succ_sub_one, pow_succ]
      ring
    rw [hdot]
    exact one_add_pow_sub_one_le hu0 (by nlinarith)
  · simpa [IsDotErr, ← sq, abs_mul_self, sq_abs] using hσ

/-- The judgment `NLAlib.Ops.RoundedScalarBlas.nrm2_meets_stdModel` read at one cell. A
corollary kept in operand form because its caller frames the tree inside a stage whose contract
states the stored cell (`NLAlib.Schur.frobNormStage`), not a reported block. -/
theorem nrm2_writes_stdModel {Op : Type} [Has ScalarOp Op] {M : Machine ℝ} {u : ℝ}
    {I : Interp Op Tst ℝ} (hS : IsScalar M I) (hM : StdModel u id M) {n : ℕ}
    (hu : ((n : ℝ) + 2) * u ≤ 1 / 2) {τ : Tape ℝ} {m : Mem ℝ} {x z : ℕ × ℕ} {xs : List ℝ}
    (hl : m.Live [x, z]) (hx : m.store.readBlock x.1 x.2 n = some xs)
    (hz : z.2 < m.store.len z.1) (hxz : x.1 ≠ z.1) :
    Writes .total I τ nrm2.body (Env.frame [n] [x, z]) (Store.inBlock z.1 z.2 1)
      (fun μ => μ.pos = m.pos ∧ ∃ v : ℝ, μ.store.get z.1 z.2 = some v ∧
        (1 - ((n : ℝ) + 2) * u) * Real.sqrt (∑ i ∈ Finset.range n, (vec xs i) ^ 2) ≤ v ∧
        v ≤ (1 + ((n : ℝ) + 2) * u) * Real.sqrt (∑ i ∈ Finset.range n, (vec xs i) ^ 2)) m := by
  have h := nrm2_meets_stdModel (Tst := Tst) hS hM [n] [x, z] τ m [xs] rfl rfl hl
    (by routine_sep) (Mem.readBlocks_of_cons hx rfl) hu
    (by routine_nf; simpa [Mem.Room] using hz)
  refine h.mono (by routine_nf; fp_sub) ?_
  rintro μ - ⟨hpos, ys, hys, hpost⟩
  routine_nf at hys
  obtain ⟨z', zs, hz', hzs, rfl⟩ := Mem.readBlocks_one hys
  obtain rfl : z = z' := by simpa using hz'
  obtain ⟨v, rfl⟩ := List.length_eq_one_iff.mp (Store.readBlock_eq_some_iff.mp hzs).1
  exact ⟨hpos, v, by simpa using Store.get_of_readBlock hzs (j := 0) Nat.one_pos 0, hpost⟩

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

/-- The scalar-lowered norm completes on any scalar machine and stores a word (the trivial model
`NLAlib.Ops.stdModel_one_zero`): a judgment with no claim on the word. -/
theorem nrm2_meets_word {Op Tst : Type} [Has ScalarOp Op] {M : Machine ℝ} {I : Interp Op Tst ℝ}
    (hS : IsScalar M I) :
    (nrm2 (Op := Op) (Tst := Tst)).Meets I (spec% [n] (xs) → ([v]) ensures True) := by
  routine_intro [n] (x, z) reads (xs)
  refine (nrm2_writes_rel (laws (stdModel_one_zero M) zero_le_one (isScalar_rename hS)).2.nrm2
    rfl rfl rfl rfl trivial (by simp [Mem.Live, hl.1, hl.2]) hxs (by omega) hxz).mono
    (by fp_sub) ?_
  rintro μ - ⟨hpos, v, hget, -⟩
  exact ⟨by simpa using hpos, [[v]],
    Mem.readBlocks_of_cons (Store.readBlock_one_of_get hget) rfl, trivial⟩

/-- The judgment `NLAlib.Ops.RoundedScalarBlas.nrm2_meets_word` read at one cell. A corollary
kept in operand form because its caller frames the tree inside a stage whose contract states
that a cell is stored (`NLAlib.Schur.frobNormStage`), not a reported block. -/
theorem nrm2_writes {Op Tst : Type} [Has ScalarOp Op]
    {M : Machine ℝ} {I : Interp Op Tst ℝ} (hS : IsScalar M I) {n : ℕ} {τ : Tape ℝ} {m : Mem ℝ}
    {x z : ℕ × ℕ} {xs : List ℝ} (hl : m.Live [x, z])
    (hx : m.store.readBlock x.1 x.2 n = some xs) (hz : z.2 < m.store.len z.1) (hxz : x.1 ≠ z.1) :
    Writes .total I τ nrm2.body (Env.frame [n] [x, z]) (Store.inBlock z.1 z.2 1)
      (fun μ => ∃ v : ℝ, μ.store.get z.1 z.2 = some v) m := by
  have h := nrm2_meets_word (Tst := Tst) hS [n] [x, z] τ m [xs] rfl rfl hl (by routine_sep)
    (Mem.readBlocks_of_cons hx rfl) trivial (by routine_nf; simpa [Mem.Room] using hz)
  refine h.mono (by routine_nf; fp_sub) ?_
  rintro μ - ⟨-, ys, hys, hpost⟩
  routine_nf at hys
  obtain ⟨z', zs, hz', hzs, rfl⟩ := Mem.readBlocks_one hys
  obtain rfl : z = z' := by simpa using hz'
  obtain ⟨v, rfl⟩ := List.length_eq_one_iff.mp (Store.readBlock_eq_some_iff.mp hzs).1
  exact ⟨v, by simpa using Store.get_of_readBlock hzs (j := 0) Nat.one_pos 0⟩

end NLAlib.Ops.RoundedScalarBlas
