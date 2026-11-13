/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Computation.RunsWithin

/-!
# Substitution: certified implementations of instructions, oracles and kernels

`NLAlib.Computation.Stmt.subst implI implO implK s` replaces every scalar instruction of `s` by the
statement `implI i`, every oracle call by `implO …` and every kernel call by `implK …`; comparisons,
index binders, read-only reads, allocations and control are kept. An implementation is certified
once: `NLAlib.Computation.ImplementsInstr` says that whenever an instruction succeeds under the
abstract interpretation, its implementation succeeds under the concrete one with the same store and
tape positions, at most a given cost of its kind, the same current memory and peaks raised by at
most a scratch; `NLAlib.Computation.ImplementsOracle` says the same of oracle calls, for every index
expression of the offsets and widths, and `NLAlib.Computation.ImplementsKernel` of kernel calls, for
every index expression of the dimensions and offsets. So a result proved against a kernel contract
becomes a result about a program whose kernel calls are certified programs.

The substitution theorem `NLAlib.Computation.RunsWithin.subst` composes them: a program that runs
within a budget under the abstract interpretation runs, substituted, under the concrete one, with
the counts substituted kind by kind (`NLAlib.Computation.substCountG`), the peak raised by the
scratch and the concrete read-only data, and the same store, tape positions and current memory as an
abstract final state. The two interpretations share one carrier and agree on comparisons,
conversions to indices and widths, and the concrete read-only data extends the abstract one, so
substitutions chain. The proof is a simulation (`NLAlib.Computation.Sim`,
`NLAlib.Computation.exec_subst_sim`) by induction on the statement. The oracle theorem
`NLAlib.Computation.RunsWithin.substOracle` is the case that keeps every instruction. Design:
`docs/design/Computation.md` (D4, D18).

## Main definitions

* `NLAlib.Computation.Stmt.subst`, `NLAlib.Computation.Stmt.substOracle`.
* `NLAlib.Computation.substCountG`, `NLAlib.Computation.substKind`,
  `NLAlib.Computation.substCount`: substituted counts.
* `NLAlib.Computation.ImplementsInstr`, `NLAlib.Computation.ImplementsOracle`,
  `NLAlib.Computation.ImplementsKernel`: certificates.

## Main results

* `NLAlib.Computation.RunsWithin.subst`: the substitution theorem.
* `NLAlib.Computation.RunsWithin.substOracle`: oracle calls replaced by an implementation.
* `NLAlib.Computation.exec_subst_sim`: the simulation.
* `NLAlib.Computation.implementsKernel_self`: the identity implementation of kernels.
-/

@[expose] public section

namespace NLAlib.Computation

section Interface
variable {P ι K : Type} [DecidableEq P]

/-- **Substitution of any node kind**: scalar instructions by `implI`, oracle calls by
`implO`, kernel calls by `implK`. Comparisons, index binders, read-only reads, allocation and
control are kept. -/
def Stmt.subst {ι' VB VI : Type} (implI : Instr P VB VI → Stmt P ι' VB VI)
    (implO : ι → P → VB → IExp VI → VB → IExp VI → IExp VI → Stmt P ι' VB VI)
    (implK : ι → P → List (IExp VI) → List (VB × IExp VI) → List (VB × IExp VI) →
      Stmt P ι' VB VI) :
    Stmt P ι VB VI → Stmt P ι' VB VI
  | .skip => .skip
  | .seq s t => .seq (s.subst implI implO implK) (t.subst implI implO implK)
  | .instr i => implI i
  | .apply o p d dOff s sOff cols => implO o p d dOff s sOff cols
  | .rom p d i => .rom p d i
  | .alloc p len body => .alloc p len fun v => (body v).subst implI implO implK
  | .loop n body => .loop n fun v => (body v).subst implI implO implK
  | .whileFuel f p c x y body => .whileFuel f p c x y (body.subst implI implO implK)
  | .ite p c x y t e => .ite p c x y (t.subst implI implO implK) (e.subst implI implO implK)
  | .named n a body => .named n a (body.subst implI implO implK)
  | .kcall o p dims ins outs => implK o p dims ins outs
  | .bindIdx p x bound body => .bindIdx p x bound fun v => (body v).subst implI implO implK

/-- Oracle substitution alone. A kernel call, whose name has no counterpart among the new
names, becomes `skip`: the oracle substitution theorem
`NLAlib.Computation.RunsWithin.substOracle` is about interpretations with no kernels, under which
no successful run makes a kernel call. -/
def Stmt.substOracle {ι' VB VI : Type}
    (impl : ι → P → VB → IExp VI → VB → IExp VI → IExp VI → Stmt P ι' VB VI) :
    Stmt P ι VB VI → Stmt P ι' VB VI :=
  Stmt.subst .instr impl fun _ _ _ _ _ => .skip

/-- Substitute a count of every kind: `n` operations of kind `k` become `n • cost k`. -/
noncomputable def substCountG {ι' : Type} (cost : OpKind P ι → OpCount P ι') :
    OpCount P ι →+ OpCount P ι' :=
  Finsupp.liftAddHom fun k => (smulAddHom ℕ (OpCount P ι')).flip (cost k)

/-- Oracle and kernel kinds by `cost`, every other kind by itself. -/
noncomputable def substKind {ι' : Type} (cost : OpKind P ι → OpCount P ι') :
    OpKind P ι → OpCount P ι'
  | .load p o => cost (.load p o)
  | .matvec p o => cost (.matvec p o)
  | .kcall p o ds => cost (.kcall p o ds)
  | .bin p b => Finsupp.single (.bin p b) 1
  | .un p u => Finsupp.single (.un p u) 1
  | .lit p => Finsupp.single (.lit p) 1
  | .cmp p => Finsupp.single (.cmp p) 1
  | .copy p => Finsupp.single (.copy p) 1
  | .draw p d => Finsupp.single (.draw p d) 1
  | .convert p q => Finsupp.single (.convert p q) 1
  | .rom p => Finsupp.single (.rom p) 1
  | .toNat p => Finsupp.single (.toNat p) 1

/-- Counts with the oracle and kernel kinds substituted by `cost` and every other kind kept. -/
noncomputable def substCount {ι' : Type} (cost : OpKind P ι → OpCount P ι') :
    OpCount P ι →+ OpCount P ι' :=
  substCountG (substKind cost)

/-- **An implementation of the scalar instructions of `I` under `I'`**: whenever an instruction
succeeds abstractly, its implementation succeeds, writes the same store and tape positions,
costs at most `cost` of its kind, keeps current memory, and raises the peaks by at most the
scratch (per tag and in bits). -/
def ImplementsInstr {ι' : Type} {C : Type} (I : Interp P ι K C)
    (I' : Interp P ι' K (OpCount P ι')) (implI : Instr P ℕ ℕ → Stmt P ι' ℕ ℕ)
    (cost : OpKind P ι → OpCount P ι') (scratch : P → ℕ) (scratchW : ℕ) : Prop :=
  ∀ (i : Instr P ℕ ℕ) (st : St P K (OpCount P ι')) (r : Store P K × (Dist → ℕ)),
    i.run I.sem I.tape st.store st.pos = some r →
    ∃ st', exec I' (implI i) st = some st' ∧ st'.store = r.1 ∧ st'.pos = r.2 ∧
      st'.cur = st.cur ∧ st'.curW = st.curW ∧ st'.cnt ≤ st.cnt + cost i.kind ∧
      (∀ q, st'.peak q ≤ max (st.peak q) (st.cur q + scratch q)) ∧
      st'.peakW ≤ max st.peakW (st.curW + scratchW)

/-- **An implementation of the oracles of `I` under `I'`**, for every index expression of the
offsets and widths, on calls whose source and destination blocks do not overlap (the run fails
on the others). -/
def ImplementsOracle {ι' : Type} (I : Interp P ι K (OpCount P ι))
    (I' : Interp P ι' K (OpCount P ι'))
    (impl : ι → P → ℕ → IExp ℕ → ℕ → IExp ℕ → IExp ℕ → Stmt P ι' ℕ ℕ)
    (cost : OpKind P ι → OpCount P ι') (scratch : P → ℕ) (scratchW : ℕ) : Prop :=
  ∀ (o : ι) (p : P) (dst : ℕ) (dOff : IExp ℕ) (src : ℕ) (sOff cols : IExp ℕ)
    (st : St P K (OpCount P ι')) (X Y : Array K) (s₁ : Store P K),
    (dst ≠ src ∨ dOff.eval + I.height o * cols.eval ≤ sOff.eval ∨
      sOff.eval + I.height o * cols.eval ≤ dOff.eval) →
    st.store.readBlock p src sOff.eval (I.height o * cols.eval) = some X →
    I.oracle o cols.eval X = some Y → st.store.writeBlock p dst dOff.eval Y = some s₁ →
    ∃ st', exec I' (impl o p dst dOff src sOff cols) st = some st' ∧ st'.store = s₁ ∧
      st'.pos = st.pos ∧ st'.cur = st.cur ∧ st'.curW = st.curW ∧
      st'.cnt ≤ st.cnt + (cost (.load p o) + cols.eval • cost (.matvec p o)) ∧
      (∀ q, st'.peak q ≤ max (st.peak q) (st.cur q + scratch q)) ∧
      st'.peakW ≤ max st.peakW (st.curW + scratchW)

/-- **An implementation of the kernels of `I` under `I'`**, for every index expression of the
dimensions and offsets: whenever a kernel call succeeds abstractly
(`NLAlib.Computation.Interp.kcallStore`, which fails on aliased calls), its implementation
succeeds, writes the same store, keeps the tape positions and current memory, costs at most
`cost` of its kind, and raises the peaks by at most the scratch (per tag and in bits). -/
def ImplementsKernel {ι' : Type} (I : Interp P ι K (OpCount P ι))
    (I' : Interp P ι' K (OpCount P ι'))
    (impl : ι → P → List (IExp ℕ) → List (ℕ × IExp ℕ) → List (ℕ × IExp ℕ) → Stmt P ι' ℕ ℕ)
    (cost : OpKind P ι → OpCount P ι') (scratch : P → ℕ) (scratchW : ℕ) : Prop :=
  ∀ (o : ι) (p : P) (dims : List (IExp ℕ)) (ins outs : List (ℕ × IExp ℕ))
    (st : St P K (OpCount P ι')) (s₁ : Store P K),
    I.kcallStore o p (dims.map IExp.eval) (ins.map fun x => (x.1, x.2.eval))
      (outs.map fun x => (x.1, x.2.eval)) st.store = some s₁ →
    ∃ st', exec I' (impl o p dims ins outs) st = some st' ∧ st'.store = s₁ ∧
      st'.pos = st.pos ∧ st'.cur = st.cur ∧ st'.curW = st.curW ∧
      st'.cnt ≤ st.cnt + cost (.kcall p o (dims.map IExp.eval)) ∧
      (∀ q, st'.peak q ≤ max (st.peak q) (st.cur q + scratch q)) ∧
      st'.peakW ≤ max st.peakW (st.curW + scratchW)

end Interface

/-! ## The composition theorem -/

section Composition
variable {P ι ι' K : Type} [DecidableEq P]

omit [DecidableEq P] in
/-- The substituted count of one kind. -/
theorem substCountG_single {cost : OpKind P ι → OpCount P ι'} (k : OpKind P ι) (n : ℕ) :
    substCountG cost (Finsupp.single k n) = n • cost k := by
  simp [substCountG]

omit [DecidableEq P] in
/-- Substitution of counts is monotone. -/
theorem substCountG_mono (cost : OpKind P ι → OpCount P ι') {c d : OpCount P ι} (h : c ≤ d) :
    substCountG cost c ≤ substCountG cost d := by
  obtain ⟨e, rfl⟩ := exists_add_of_le h
  rw [map_add]
  exact le_self_add

/-- The simulation relation between an abstract state and a concrete one. -/
structure Sim (cost : OpKind P ι → OpCount P ι') (scratch : P → ℕ) (scratchW : ℕ)
    (st : St P K (OpCount P ι)) (st' : St P K (OpCount P ι')) : Prop where
  /-- Equal stores. -/
  store : st'.store = st.store
  /-- Equal tape positions. -/
  pos : st'.pos = st.pos
  /-- Equal current memory in cells. -/
  cur : st'.cur = st.cur
  /-- Equal current memory in bits. -/
  curW : st'.curW = st.curW
  /-- The concrete count is at most the substituted abstract count. -/
  cnt : st'.cnt ≤ substCountG cost st.cnt
  /-- The concrete peak is at most the abstract peak plus the scratch. -/
  peak : ∀ q, st'.peak q ≤ st.peak q + scratch q
  /-- The concrete bit peak is at most the abstract one plus the bit scratch. -/
  peakW : st'.peakW ≤ st.peakW + scratchW
  /-- Abstract current memory is at most its peak. -/
  curPeak : ∀ q, st.cur q ≤ st.peak q
  /-- Abstract current bit memory is at most its peak. -/
  curPeakW : st.curW ≤ st.peakW

variable {I : Interp P ι K (OpCount P ι)} {I' : Interp P ι' K (OpCount P ι')}
  {implI : Instr P ℕ ℕ → Stmt P ι' ℕ ℕ}
  {implO : ι → P → ℕ → IExp ℕ → ℕ → IExp ℕ → IExp ℕ → Stmt P ι' ℕ ℕ}
  {implK : ι → P → List (IExp ℕ) → List (ℕ × IExp ℕ) → List (ℕ × IExp ℕ) → Stmt P ι' ℕ ℕ}
  {cost : OpKind P ι → OpCount P ι'} {scratch : P → ℕ} {scratchW : ℕ}

/-- A comparison step keeps the simulation. -/
theorem cmpStep_sim (hcmp : I'.sem.cmp = I.sem.cmp) (hc : IsUnitCharge I)
    (hc' : IsUnitCharge I')
    (hcostCmp : ∀ p, cost (.cmp p) = Finsupp.single (.cmp p) 1) {p : P} {c : CmpOp}
    {x y : Cell ℕ ℕ} {st : St P K (OpCount P ι)} {st' : St P K (OpCount P ι')}
    (h : Sim cost scratch scratchW st st') {b : Bool} {st₁ : St P K (OpCount P ι)}
    (hr : cmpStep I p c x y st = some (b, st₁)) :
    ∃ st₁', cmpStep I' p c x y st' = some (b, st₁') ∧ Sim cost scratch scratchW st₁ st₁' := by
  simp only [cmpStep, Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq] at hr
  obtain ⟨a, ha, b', hb', r, hr', rfl, rfl⟩ := hr
  refine ⟨{ st' with cnt := st'.cnt + I'.charge (.cmp p) }, ?_, ?_⟩
  · simp only [cmpStep, h.store, hcmp, ha, hb', hr', Option.bind_some, Option.map_some]
  · refine { store := h.store, pos := h.pos, cur := h.cur, curW := h.curW, peak := h.peak,
             peakW := h.peakW, curPeak := h.curPeak, curPeakW := h.curPeakW, cnt := ?_ }
    change st'.cnt + I'.charge (.cmp p) ≤ substCountG cost (st.cnt + I.charge (.cmp p))
    rw [hc.charge_eq, hc'.charge_eq, map_add, substCountG_single, one_smul, hcostCmp]
    exact add_le_add h.cnt le_rfl

/-- A conversion step keeps the simulation. -/
theorem toNatStep_sim (htoNat : I'.sem.toNat = I.sem.toNat)
    (hc : IsUnitCharge I) (hc' : IsUnitCharge I')
    (hcostToNat : ∀ p, cost (.toNat p) = Finsupp.single (.toNat p) 1) {p : P} {x : Cell ℕ ℕ}
    {st : St P K (OpCount P ι)} {st' : St P K (OpCount P ι')}
    (h : Sim cost scratch scratchW st st') {k : ℕ} {st₁ : St P K (OpCount P ι)}
    (hr : toNatStep I p x st = some (k, st₁)) :
    ∃ st₁', toNatStep I' p x st' = some (k, st₁') ∧ Sim cost scratch scratchW st₁ st₁' := by
  simp only [toNatStep, Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq] at hr
  obtain ⟨a, ha, k', hk', rfl, rfl⟩ := hr
  refine ⟨{ st' with cnt := st'.cnt + I'.charge (.toNat p) }, ?_, ?_⟩
  · simp only [toNatStep, h.store, htoNat, ha, hk', Option.bind_some, Option.map_some]
  · refine { store := h.store, pos := h.pos, cur := h.cur, curW := h.curW, peak := h.peak,
             peakW := h.peakW, curPeak := h.curPeak, curPeakW := h.curPeakW, cnt := ?_ }
    change st'.cnt + I'.charge (.toNat p) ≤ substCountG cost (st.cnt + I.charge (.toNat p))
    rw [hc.charge_eq, hc'.charge_eq, map_add, substCountG_single, one_smul, hcostToNat]
    exact add_le_add h.cnt le_rfl

/-- The simulation property of a pair of statements: from related states, a successful abstract
run is matched by a successful concrete run, and the final states are related. -/
private abbrev SimRun (I : Interp P ι K (OpCount P ι)) (I' : Interp P ι' K (OpCount P ι'))
    (cost : OpKind P ι → OpCount P ι') (scratch : P → ℕ) (scratchW : ℕ) (s : Stmt P ι ℕ ℕ)
    (s' : Stmt P ι' ℕ ℕ) : Prop :=
  ∀ (st st₁ : St P K (OpCount P ι)) (st' : St P K (OpCount P ι')),
    Sim cost scratch scratchW st st' → exec I s st = some st₁ →
      ∃ st₁', exec I' s' st' = some st₁' ∧ Sim cost scratch scratchW st₁ st₁'

private theorem simRun_instr (hc : IsUnitCharge I)
    (himplI : ImplementsInstr I I' implI cost scratch scratchW) (i : Instr P ℕ ℕ) :
    SimRun I I' cost scratch scratchW (.instr i) (implI i) := by
  intro st st₁ st' h hrun
  simp only [exec, Option.map_eq_some_iff] at hrun
  obtain ⟨r, hr, rfl⟩ := hrun
  rw [← h.store, ← h.pos] at hr
  obtain ⟨st₁', hrun', hst, hpos, hcur, hcurW, hcnt, hpeak, hpeakW⟩ := himplI i st' r hr
  refine ⟨st₁', hrun', ⟨hst, hpos, hcur.trans h.cur, hcurW.trans h.curW, ?_, ?_, ?_,
    h.curPeak, h.curPeakW⟩⟩
  · refine hcnt.trans ?_
    change _ ≤ substCountG cost (st.cnt + I.charge i.kind)
    rw [hc.charge_eq, map_add, substCountG_single, one_smul]
    exact add_le_add h.cnt le_rfl
  · intro q
    refine (hpeak q).trans (max_le (h.peak q) ?_)
    rw [h.cur]
    exact Nat.add_le_add_right (h.curPeak q) _
  · refine hpeakW.trans (max_le h.peakW ?_)
    rw [h.curW]
    exact Nat.add_le_add_right h.curPeakW _

private theorem simRun_apply (hc : IsUnitCharge I)
    (himplO : ImplementsOracle I I' implO cost scratch scratchW) (o : ι) (p : P) (dst : ℕ)
    (dOff : IExp ℕ) (src : ℕ) (sOff cols : IExp ℕ) :
    SimRun I I' cost scratch scratchW (.apply o p dst dOff src sOff cols)
      (implO o p dst dOff src sOff cols) := by
  intro st st₁ st' h hrun
  simp only [exec] at hrun
  split_ifs at hrun with hdisj
  simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at hrun
  obtain ⟨X, hX, Y, hY, s₁, hs₁, rfl⟩ := hrun
  rw [← h.store] at hX hs₁
  obtain ⟨st₁', hrun', hst, hpos, hcur, hcurW, hcnt, hpeak, hpeakW⟩ :=
    himplO o p dst dOff src sOff cols st' X Y s₁ hdisj hX hY hs₁
  refine ⟨st₁', hrun', ⟨hst, hpos.trans h.pos, hcur.trans h.cur, hcurW.trans h.curW, ?_, ?_,
    ?_, h.curPeak, h.curPeakW⟩⟩
  · refine hcnt.trans ?_
    change _ ≤ substCountG cost
      (st.cnt + (I.charge (.load p o) + cols.eval • I.charge (.matvec p o)))
    rw [hc.charge_eq, map_add, map_add, map_nsmul, substCountG_single,
      substCountG_single, one_smul, one_smul]
    exact add_le_add h.cnt le_rfl
  · intro q
    refine (hpeak q).trans (max_le (h.peak q) ?_)
    rw [h.cur]
    exact Nat.add_le_add_right (h.curPeak q) _
  · refine hpeakW.trans (max_le h.peakW ?_)
    rw [h.curW]
    exact Nat.add_le_add_right h.curPeakW _

private theorem simRun_kcall (hc : IsUnitCharge I)
    (himplK : ImplementsKernel I I' implK cost scratch scratchW) (o : ι) (p : P)
    (dims : List (IExp ℕ)) (ins outs : List (ℕ × IExp ℕ)) :
    SimRun I I' cost scratch scratchW (.kcall o p dims ins outs) (implK o p dims ins outs) := by
  intro st st₁ st' h hrun
  simp only [exec, Option.map_eq_some_iff] at hrun
  obtain ⟨s₁, hs₁, rfl⟩ := hrun
  rw [← h.store] at hs₁
  obtain ⟨st₁', hrun', hst, hpos, hcur, hcurW, hcnt, hpeak, hpeakW⟩ :=
    himplK o p dims ins outs st' s₁ hs₁
  refine ⟨st₁', hrun', ⟨hst, hpos.trans h.pos, hcur.trans h.cur, hcurW.trans h.curW, ?_, ?_,
    ?_, h.curPeak, h.curPeakW⟩⟩
  · refine hcnt.trans ?_
    change _ ≤ substCountG cost (st.cnt + I.charge (.kcall p o (dims.map IExp.eval)))
    rw [hc.charge_eq, map_add, substCountG_single, one_smul]
    exact add_le_add h.cnt le_rfl
  · intro q
    refine (hpeak q).trans (max_le (h.peak q) ?_)
    rw [h.cur]
    exact Nat.add_le_add_right (h.curPeak q) _
  · refine hpeakW.trans (max_le h.peakW ?_)
    rw [h.curW]
    exact Nat.add_le_add_right h.curPeakW _

private theorem simRun_rom (hc : IsUnitCharge I)
    (hc' : IsUnitCharge I')
    (hrom : ∀ i v, I.rom i = some v → I'.rom i = some v)
    (hcostRom : ∀ p, cost (.rom p) = Finsupp.single (.rom p) 1) (p : P) (dst : Cell ℕ ℕ)
    (i : IExp ℕ) : SimRun I I' cost scratch scratchW (.rom p dst i) (.rom p dst i) := by
  intro st st₁ st' h hrun
  simp only [exec, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hrun
  obtain ⟨v, hv, s₁, hs₁, rfl⟩ := hrun
  refine ⟨{ st' with store := s₁, cnt := st'.cnt + I'.charge (.rom p) }, ?_, ?_⟩
  · simp only [exec, hrom _ _ hv, Option.bind_some, h.store, hs₁, Option.map_some]
  · refine { store := rfl, pos := h.pos, cur := h.cur, curW := h.curW, peak := h.peak,
             peakW := h.peakW, curPeak := h.curPeak, curPeakW := h.curPeakW, cnt := ?_ }
    change st'.cnt + I'.charge (.rom p) ≤ substCountG cost (st.cnt + I.charge (.rom p))
    rw [hc.charge_eq, hc'.charge_eq, map_add, substCountG_single, one_smul, hcostRom]
    exact add_le_add h.cnt le_rfl

private theorem simRun_alloc (hwidth : I'.width = I.width) (p : P) (len : IExp ℕ)
    (body : ℕ → Stmt P ι ℕ ℕ) (body' : ℕ → Stmt P ι' ℕ ℕ)
    (ih : ∀ v, SimRun I I' cost scratch scratchW (body v) (body' v)) :
    SimRun I I' cost scratch scratchW (.alloc p len body) (.alloc p len body') := by
  intro st st₁ st' h hrun
  simp only [exec, Option.map_eq_some_iff] at hrun
  obtain ⟨st₂, h₂, rfl⟩ := hrun
  have hsim : Sim cost scratch scratchW
      { st with
        store := st.store.push (p, Array.replicate len.eval none)
        cur := Function.update st.cur p (st.cur p + len.eval)
        peak := Function.update st.peak p (max (st.peak p) (st.cur p + len.eval))
        curW := st.curW + len.eval * I.width p
        peakW := max st.peakW (st.curW + len.eval * I.width p) }
      { st' with
        store := st'.store.push (p, Array.replicate len.eval none)
        cur := Function.update st'.cur p (st'.cur p + len.eval)
        peak := Function.update st'.peak p (max (st'.peak p) (st'.cur p + len.eval))
        curW := st'.curW + len.eval * I'.width p
        peakW := max st'.peakW (st'.curW + len.eval * I'.width p) } := by
    refine { store := by simp only [h.store], pos := h.pos, cur := by simp only [h.cur],
             curW := by simp only [h.curW, hwidth], cnt := h.cnt, peak := fun q => ?_,
             peakW := ?_, curPeak := fun q => ?_, curPeakW := le_max_right _ _ }
    · rcases eq_or_ne q p with rfl | hq
      · simp only [Function.update_self, h.cur]
        exact max_le ((h.peak q).trans (Nat.add_le_add_right (le_max_left _ _) _))
          (le_add_right (le_max_right _ _))
      · simp only [Function.update_of_ne hq]
        exact h.peak q
    · simp only [h.curW, hwidth]
      exact max_le (h.peakW.trans (Nat.add_le_add_right (le_max_left _ _) _))
        (le_add_right (le_max_right _ _))
    · rcases eq_or_ne q p with rfl | hq
      · simp only [Function.update_self]
        exact le_max_right _ _
      · simp only [Function.update_of_ne hq]
        exact h.curPeak q
  have hsize : st'.store.size = st.store.size := by rw [h.store]
  obtain ⟨st₂', h₂', hs₂⟩ := ih st.store.size _ st₂ _ hsim h₂
  refine ⟨{ st₂' with
    store := Array.pop st₂'.store
    cur := Function.update st₂'.cur p (st₂'.cur p - len.eval)
    curW := st₂'.curW - len.eval * I'.width p }, ?_, ?_⟩
  · simp only [exec, hsize, h₂', Option.map_some]
  · exact { store := by simp only [hs₂.store]
            pos := hs₂.pos
            cur := by simp only [hs₂.cur]
            curW := by simp only [hs₂.curW, hwidth]
            cnt := hs₂.cnt
            peak := hs₂.peak
            peakW := hs₂.peakW
            curPeak := fun q => by
              rcases eq_or_ne q p with rfl | hq
              · simp only [Function.update_self]
                exact (Nat.sub_le _ _).trans (hs₂.curPeak q)
              · simp only [Function.update_of_ne hq]
                exact hs₂.curPeak q
            curPeakW := (Nat.sub_le _ _).trans hs₂.curPeakW }

private theorem simRun_loop (n : IExp ℕ) (body : ℕ → Stmt P ι ℕ ℕ)
    (body' : ℕ → Stmt P ι' ℕ ℕ) (ih : ∀ v, SimRun I I' cost scratch scratchW (body v) (body' v)) :
    SimRun I I' cost scratch scratchW (.loop n body) (.loop n body') := by
  intro st st₁ st' h hrun
  simp only [exec] at hrun
  simp only [exec]
  generalize List.range n.eval = l at hrun ⊢
  induction l generalizing st st' with
  | nil =>
    simp only [List.foldlM_nil, pure, Option.some.injEq] at hrun ⊢
    subst hrun
    exact ⟨st', rfl, h⟩
  | cons i l ihl =>
    simp only [List.foldlM_cons] at hrun ⊢
    change ((exec I (body i) st).bind fun st => List.foldlM _ st l) = some st₁ at hrun
    rw [Option.bind_eq_some_iff] at hrun
    obtain ⟨st₂, h₂, h₃⟩ := hrun
    obtain ⟨st₂', h₂', hs₂⟩ := ih i st st₂ st' h h₂
    obtain ⟨st₃', h₃', hs₃⟩ := ihl st₂ st₂' hs₂ h₃
    refine ⟨st₃', ?_, hs₃⟩
    change ((exec I' (body' i) st').bind fun st => List.foldlM _ st l) = _
    rw [h₂', Option.bind_some]
    exact h₃'

/-- One pass of the guarded loop of `whileFuel` keeps the simulation. -/
private theorem simRun_whileFuel_fold (hcmp : I'.sem.cmp = I.sem.cmp)
    (hc : IsUnitCharge I) (hc' : IsUnitCharge I')
    (hcostCmp : ∀ p, cost (.cmp p) = Finsupp.single (.cmp p) 1) (p : P) (c : CmpOp)
    (x y : Cell ℕ ℕ) (body : Stmt P ι ℕ ℕ) (body' : Stmt P ι' ℕ ℕ)
    (ih : SimRun I I' cost scratch scratchW body body') :
    ∀ (l : List ℕ) (s : St P K (OpCount P ι) × Bool)
      (s' : St P K (OpCount P ι') × Bool) (r : St P K (OpCount P ι) × Bool),
      Sim cost scratch scratchW s.1 s'.1 → s.2 = s'.2 →
      l.foldlM (fun (s : St P K (OpCount P ι) × Bool) _ =>
        if s.2 then (cmpStep I p c x y s.1).bind fun r =>
          if r.1 then (exec I body r.2).map fun st' => (st', true) else some (r.2, false)
        else some s) s = some r →
      ∃ r', l.foldlM (fun (s : St P K (OpCount P ι') × Bool) _ =>
        if s.2 then (cmpStep I' p c x y s.1).bind fun r =>
          if r.1 then (exec I' body' r.2).map fun st' => (st', true)
          else some (r.2, false)
        else some s) s' = some r' ∧ Sim cost scratch scratchW r.1 r'.1 ∧ r.2 = r'.2 := by
  intro l
  induction l with
  | nil =>
    intro s s' r hs hb hr
    simp only [List.foldlM_nil, pure, Option.some.injEq] at hr
    subst hr
    exact ⟨s', rfl, hs, hb⟩
  | cons j l ihl =>
    intro s s' r hs hb hr
    simp only [List.foldlM_cons] at hr ⊢
    change (Option.bind _ fun s => List.foldlM _ s l) = some r at hr
    rw [Option.bind_eq_some_iff] at hr
    obtain ⟨s₂, h₂, h₃⟩ := hr
    obtain ⟨s₁, b₁⟩ := s
    obtain ⟨s₁', b₁'⟩ := s'
    simp only at hb hs
    subst hb
    cases b₁ with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at h₂
      subst h₂
      obtain ⟨r', h', hr', hb'⟩ := ihl _ (s₁', false) r hs rfl h₃
      exact ⟨r', by simpa using h', hr', hb'⟩
    | true =>
      simp only [↓reduceIte, Option.bind_eq_some_iff] at h₂
      obtain ⟨⟨bc, sc⟩, hcmpS, h₄⟩ := h₂
      obtain ⟨sc', hcmp', hsc⟩ := cmpStep_sim hcmp hc hc' hcostCmp hs hcmpS
      cases bc with
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at h₄
        subst h₄
        obtain ⟨r', h', hr', hb'⟩ := ihl _ (sc', false) r hsc rfl h₃
        refine ⟨r', ?_, hr', hb'⟩
        change (Option.bind _ fun s => List.foldlM _ s l) = some r'
        simp only [↓reduceIte, hcmp', Option.bind_some, Bool.false_eq_true]
        exact h'
      | true =>
        simp only [↓reduceIte, Option.map_eq_some_iff] at h₄
        obtain ⟨sb, hsb, rfl⟩ := h₄
        obtain ⟨sb', hsb', hsimb⟩ := ih sc sb sc' hsc hsb
        obtain ⟨r', h', hr', hb'⟩ := ihl _ (sb', true) r hsimb rfl h₃
        refine ⟨r', ?_, hr', hb'⟩
        change (Option.bind _ fun s => List.foldlM _ s l) = some r'
        simp only [↓reduceIte, hcmp', Option.bind_some, hsb', Option.map_some]
        exact h'

private theorem simRun_whileFuel (hcmp : I'.sem.cmp = I.sem.cmp)
    (hc : IsUnitCharge I) (hc' : IsUnitCharge I')
    (hcostCmp : ∀ p, cost (.cmp p) = Finsupp.single (.cmp p) 1) (fuel : IExp ℕ) (p : P)
    (c : CmpOp) (x y : Cell ℕ ℕ) (body : Stmt P ι ℕ ℕ) (body' : Stmt P ι' ℕ ℕ)
    (ih : SimRun I I' cost scratch scratchW body body') :
    SimRun I I' cost scratch scratchW (.whileFuel fuel p c x y body)
      (.whileFuel fuel p c x y body') := by
  intro st st₁ st' h hrun
  simp only [exec, Option.bind_eq_some_iff] at hrun
  obtain ⟨r, hr, hfin⟩ := hrun
  simp only [exec]
  obtain ⟨r', hr', hsim, hb⟩ := simRun_whileFuel_fold hcmp hc hc' hcostCmp p c x y body body' ih
    _ (st, true) (st', true) r h rfl hr
  cases hrb : r.2 with
  | true => simp [hrb] at hfin
  | false =>
    simp only [hrb, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hfin
    subst hfin
    refine ⟨r'.1, ?_, hsim⟩
    rw [Option.bind_eq_some_iff]
    exact ⟨r', hr', by simp [← hb, hrb]⟩

private theorem simRun_bindIdx (htoNat : I'.sem.toNat = I.sem.toNat)
    (hc : IsUnitCharge I) (hc' : IsUnitCharge I')
    (hcostToNat : ∀ p, cost (.toNat p) = Finsupp.single (.toNat p) 1) (p : P) (x : Cell ℕ ℕ)
    (bound : IExp ℕ) (body : ℕ → Stmt P ι ℕ ℕ) (body' : ℕ → Stmt P ι' ℕ ℕ)
    (ih : ∀ v, SimRun I I' cost scratch scratchW (body v) (body' v)) :
    SimRun I I' cost scratch scratchW (.bindIdx p x bound body) (.bindIdx p x bound body') := by
  intro st st₁ st' h hrun
  simp only [exec, Option.bind_eq_some_iff] at hrun
  obtain ⟨⟨k, st₂⟩, hk, h₂⟩ := hrun
  obtain ⟨st₂', hk', hs₂⟩ := toNatStep_sim htoNat hc hc' hcostToNat h hk
  split_ifs at h₂ with hle
  obtain ⟨st₃', h₃', hs₃⟩ := ih _ st₂ st₁ st₂' hs₂ h₂
  exact ⟨st₃', by simp only [exec, hk', Option.bind_some, if_pos hle]; exact h₃', hs₃⟩

/-- The simulation, by induction on the statement: from related states, a successful
abstract run of `s` is matched by a successful concrete run of `s.subst implI implO implK`, and
the final states are related. -/
theorem exec_subst_sim (hcmp : I'.sem.cmp = I.sem.cmp) (htoNat : I'.sem.toNat = I.sem.toNat)
    (hc : IsUnitCharge I) (hc' : IsUnitCharge I')
    (hwidth : I'.width = I.width) (hrom : ∀ i v, I.rom i = some v → I'.rom i = some v)
    (hcostCmp : ∀ p, cost (.cmp p) = Finsupp.single (.cmp p) 1)
    (hcostRom : ∀ p, cost (.rom p) = Finsupp.single (.rom p) 1)
    (hcostToNat : ∀ p, cost (.toNat p) = Finsupp.single (.toNat p) 1)
    (himplI : ImplementsInstr I I' implI cost scratch scratchW)
    (himplO : ImplementsOracle I I' implO cost scratch scratchW)
    (himplK : ImplementsKernel I I' implK cost scratch scratchW) :
    ∀ (s : Stmt P ι ℕ ℕ) (st st₁ : St P K (OpCount P ι)) (st' : St P K (OpCount P ι')),
      Sim cost scratch scratchW st st' → exec I s st = some st₁ →
      ∃ st₁', exec I' (s.subst implI implO implK) st' = some st₁' ∧
        Sim cost scratch scratchW st₁ st₁' := by
  intro s
  induction s with
  | skip =>
    intro st st₁ st' h hrun
    simp only [exec, Option.some.injEq] at hrun
    subst hrun
    exact ⟨st', rfl, h⟩
  | seq s t ihs iht =>
    intro st st₁ st' h hrun
    simp only [exec, Option.bind_eq_some_iff] at hrun
    obtain ⟨st₂, h₂, h₃⟩ := hrun
    obtain ⟨st₂', h₂', hs₂⟩ := ihs st st₂ st' h h₂
    obtain ⟨st₃', h₃', hs₃⟩ := iht st₂ st₁ st₂' hs₂ h₃
    exact ⟨st₃', by simp only [Stmt.subst, exec, h₂', Option.bind_some, h₃'], hs₃⟩
  | instr i => exact simRun_instr hc himplI i
  | apply o p dst dOff src sOff cols => exact simRun_apply hc himplO o p dst dOff src sOff cols
  | rom p dst i => exact simRun_rom hc hc' hrom hcostRom p dst i
  | alloc p len body ih => exact simRun_alloc hwidth p len body _ ih
  | loop n body ih => exact simRun_loop n body _ ih
  | whileFuel fuel p c x y body ih =>
    exact simRun_whileFuel hcmp hc hc' hcostCmp fuel p c x y body _ ih
  | ite p c x y t e iht ihe =>
    intro st st₁ st' h hrun
    simp only [exec, Option.bind_eq_some_iff] at hrun
    obtain ⟨⟨b, st₂⟩, hcmpS, h₂⟩ := hrun
    obtain ⟨st₂', hcmp', hs₂⟩ := cmpStep_sim hcmp hc hc' hcostCmp h hcmpS
    simp only [Stmt.subst, exec, hcmp', Option.bind_some]
    cases b with
    | true =>
      simp only [↓reduceIte] at h₂ ⊢
      exact iht st₂ st₁ st₂' hs₂ h₂
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at h₂ ⊢
      exact ihe st₂ st₁ st₂' hs₂ h₂
  | named name args body ih =>
    intro st st₁ st' h hrun
    exact ih st st₁ st' h hrun
  | kcall o p dims ins outs => exact simRun_kcall hc himplK o p dims ins outs
  | bindIdx p x bound body ih => exact simRun_bindIdx htoNat hc hc' hcostToNat p x bound body _ ih

/-- Move a state to another count type. -/
def St.withCnt {C C' : Type} (st : St P K C) (c : C') : St P K C' :=
  { store := st.store, pos := st.pos, cnt := c, cur := st.cur, peak := st.peak,
    curW := st.curW, peakW := st.peakW }

/-- **The substitution theorem**: scalar instructions, oracle calls and kernel calls replaced by
certified implementations. Let a program run within the budget `c`, `m` under the abstract
interpretation `I`, from a state with zero counts and current memory at most its peak, and let
`implI`, `implO` and `implK` implement the instructions, oracles and kernels of `I` under `I'` at
cost `cost` with scratch `scratch` (cells per tag) and `scratchW` (bits). If both interpretations
charge one per operation, agree on comparisons, conversions to indices and widths, the concrete
read-only data extends the abstract one, and comparisons, conversions to indices and read-only
reads cost themselves, then the substituted program
succeeds under `I'` with counts at most `substCountG cost c`, peak at most `m q + scratch q` plus
the concrete read-only data at each tag, and the store, tape positions and current memory of an
abstract final state satisfying the postcondition, whose bit peak it exceeds by at most `scratchW`.
No printed source.
Result: computation-substitution -/
theorem RunsWithin.subst (hcmp : I'.sem.cmp = I.sem.cmp) (htoNat : I'.sem.toNat = I.sem.toNat)
    (hc : IsUnitCharge I) (hc' : IsUnitCharge I')
    (hwidth : I'.width = I.width) (hrom : ∀ i v, I.rom i = some v → I'.rom i = some v)
    (hcostCmp : ∀ p, cost (.cmp p) = Finsupp.single (.cmp p) 1)
    (hcostRom : ∀ p, cost (.rom p) = Finsupp.single (.rom p) 1)
    (hcostToNat : ∀ p, cost (.toNat p) = Finsupp.single (.toNat p) 1)
    (himplI : ImplementsInstr I I' implI cost scratch scratchW)
    (himplO : ImplementsOracle I I' implO cost scratch scratchW)
    (himplK : ImplementsKernel I I' implK cost scratch scratchW)
    {s : Stmt P ι ℕ ℕ} {st₀ : St P K (OpCount P ι)} (h0 : st₀.cnt = 0)
    (hcp : ∀ q, st₀.cur q ≤ st₀.peak q) (hcpW : st₀.curW ≤ st₀.peakW) {c : OpCount P ι}
    {m : P → ℕ} {Q : St P K (OpCount P ι) → Prop} (h : RunsWithin I s st₀ c m Q) :
    ∃ st₁', exec I' (s.subst implI implO implK) (st₀.withCnt 0) = some st₁' ∧
      st₁'.cnt ≤ substCountG cost c ∧
      (∀ q, st₁'.peak q + I'.romSize q ≤ m q + scratch q + I'.romSize q) ∧
      (∃ st, Q st ∧ st₁'.store = st.store ∧ st₁'.pos = st.pos ∧ st₁'.cur = st.cur ∧
        st₁'.peakW ≤ st.peakW + scratchW) := by
  obtain ⟨st₁, hrun, hcnt, hpeak, hQ⟩ := h
  have hsim : Sim cost scratch scratchW st₀ (st₀.withCnt 0) :=
    { store := rfl, pos := rfl, cur := rfl, curW := rfl, cnt := by simp [St.withCnt, h0],
      peak := fun q => le_self_add, peakW := le_self_add, curPeak := hcp, curPeakW := hcpW }
  obtain ⟨st₁', hrun', hs⟩ :=
    exec_subst_sim hcmp htoNat hc hc' hwidth hrom hcostCmp hcostRom hcostToNat himplI himplO
      himplK s _ _ _ hsim
      hrun
  refine ⟨st₁', hrun', ?_, fun q => ?_, st₁, hQ, hs.store, hs.pos, hs.cur, hs.peakW⟩
  · rw [h0, zero_add] at hcnt
    exact hs.cnt.trans (substCountG_mono cost hcnt)
  · have h1 := hpeak q
    have h2 := hs.peak q
    omega

/-- The identity implementation of instructions, when the semantics and tapes agree. -/
theorem implementsInstr_self (hsem : I'.sem = I.sem) (htape : I'.tape = I.tape)
    (hc' : IsUnitCharge I') (cost : OpKind P ι → OpCount P ι')
    (hcost : ∀ i : Instr P ℕ ℕ, cost i.kind = Finsupp.single i.kind 1) :
    ImplementsInstr I I' .instr cost (fun _ => 0) 0 := by
  intro i st r hr
  refine ⟨{ st with store := r.1, pos := r.2, cnt := st.cnt + I'.charge i.kind }, ?_, rfl, rfl,
    rfl, rfl, ?_, fun q => le_max_left _ _, le_max_left _ _⟩
  · simp only [exec, hsem, htape, hr, Option.map_some]
  · simp only [hc'.charge_eq, hcost, le_refl]

/-- **The oracle substitution theorem**: oracle calls replaced by a certified implementation,
every instruction kept. Let a program run within the budget `c`, `m` under `I`, which has no
read-only data and no kernels, from a state with zero counts and current memory at most its peak,
and let `implO` implement the oracles of `I` under `I'` at cost `substKind cost` with scratch
`scratch` and `scratchW`. If the two interpretations have the same semantics, tapes and widths and
charge one per operation, the substituted program runs within the counts `substCount cost c` and
the memory `m q + scratch q` plus the concrete read-only data at each tag, and ends with the store,
tape positions and current memory of an abstract final state satisfying the postcondition. The case
of `NLAlib.Computation.RunsWithin.subst` with the identity implementation of instructions.
No printed source.
Result: computation-oracle-substitution -/
theorem RunsWithin.substOracle (hsem : I'.sem = I.sem) (htape : I'.tape = I.tape)
    (hc : IsUnitCharge I) (hc' : IsUnitCharge I')
    (hwidth : I'.width = I.width) (hrom : ∀ i, I.rom i = none)
    (hker : ∀ o ds xs, I.kernel o ds xs = none)
    (himpl : ImplementsOracle I I' implO (substKind cost) scratch scratchW)
    {s : Stmt P ι ℕ ℕ} {st₀ : St P K (OpCount P ι)} (h0 : st₀.cnt = 0)
    (hcp : ∀ q, st₀.cur q ≤ st₀.peak q) (hcpW : st₀.curW ≤ st₀.peakW) {c : OpCount P ι}
    {m : P → ℕ} {Q : St P K (OpCount P ι) → Prop} (h : RunsWithin I s st₀ c m Q) :
    RunsWithin I' (s.substOracle implO) (st₀.withCnt 0) (substCount cost c)
      (fun q => m q + scratch q + I'.romSize q)
      (fun st' => ∃ st, Q st ∧ st'.store = st.store ∧ st'.pos = st.pos ∧ st'.cur = st.cur) := by
  have hI : ImplementsInstr I I' .instr (substKind cost) scratch scratchW := by
    intro i st r hr
    obtain ⟨st', h1, h2, h3, h4, h5, h6, h7, h8⟩ :=
      implementsInstr_self (I := I) (I' := I') hsem htape hc' (substKind cost)
        (fun i => by cases i <;> rfl) i st r hr
    exact ⟨st', h1, h2, h3, h4, h5, h6, fun q => (h7 q).trans (max_le_max le_rfl le_self_add),
      h8.trans (max_le_max le_rfl le_self_add)⟩
  have hK : ImplementsKernel I I' (fun _ _ _ _ _ => .skip) (substKind cost) scratch scratchW := by
    intro o p dims ins outs st s₁ hs₁
    unfold Interp.kcallStore at hs₁
    split_ifs at hs₁
    obtain ⟨xs, -, hs₁⟩ := Option.bind_eq_some_iff.mp hs₁
    simp [hker] at hs₁
  obtain ⟨st₁', hrun, hcnt, hpeak, st, hQ, hs, hp, hcur, -⟩ :=
    RunsWithin.subst (by rw [hsem]) (by rw [hsem]) hc hc' hwidth
      (fun i v hv => by simp [hrom i] at hv) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) hI himpl
      hK h0 hcp hcpW h
  refine ⟨st₁', hrun, ?_, hpeak, st, hQ, hs, hp, hcur⟩
  change st₁'.cnt ≤ 0 + substCountG (substKind cost) c
  rw [zero_add]
  exact hcnt

end Composition

/-! ### The identity implementation of kernels -/

section KernelSelf

variable {P ι K : Type} [DecidableEq P]

/-- The identity implementation of kernels: if two interpretations over the same kernel names
have the same kernels and shapes, the concrete one charges one per operation, and `cost` charges a
kernel call itself, then keeping every kernel call implements the kernels of `I` under `I'`, with no
scratch. No printed source. -/
theorem implementsKernel_self {I I' : Interp P ι K (OpCount P ι)} (hker : I'.kernel = I.kernel)
    (hksh : I'.kshape = I.kshape) (hc' : IsUnitCharge I')
    (cost : OpKind P ι → OpCount P ι)
    (hcost : ∀ p o ds, cost (.kcall p o ds) = Finsupp.single (.kcall p o ds) 1) :
    ImplementsKernel I I' .kcall cost (fun _ => 0) 0 := by
  intro o p dims ins outs st s₁ hs₁
  have hk : ∀ o p ds ins outs s, I'.kcallStore o p ds ins outs s = I.kcallStore o p ds ins outs s :=
    fun o p ds ins outs s => by simp only [Interp.kcallStore, hker, hksh]
  refine ⟨{ st with store := s₁, cnt := st.cnt + I'.charge (.kcall p o (dims.map IExp.eval)) },
    ?_, rfl, rfl, rfl, rfl, ?_, fun q => le_max_left _ _, le_max_left _ _⟩
  · simp only [exec, hk, hs₁, Option.map_some]
  · simp only [hc'.charge_eq, hcost, le_refl]

end KernelSelf

end NLAlib.Computation
