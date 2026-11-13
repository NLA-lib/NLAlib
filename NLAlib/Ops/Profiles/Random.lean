/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Catalog.Random
public import NLAlib.Ops.Profile

/-!
# Profile: the vector draw by scalar draws

`NLAlib.Ops.Rand.gaussLoop` implements the vector draw `gauss [n] [] [g]` by a loop of `n`
scalar draws and keeps every other operation.

## Main results

* `NLAlib.Ops.Rand.gaussLoopImpl_spec`: the loop meets the contract of the vector draw.
* `NLAlib.Ops.Rand.gaussLoop_certifies`: the certificate: the contract of the vector draw, the
  counts (`n` draws), and the tape window by the window lemma: the `n` entries the loop reads
  are the window that the law of the tape assigns to the call.
-/

@[expose] public section

namespace NLAlib.Ops.Rand

variable {K Tst : Type}

/-- **The vector draw by a loop of scalar draws.** Index variables: `n`, the offset of `g`, then
the loop variable; buffer variable: `g`. -/
def gaussLoopImpl : Impl ROp Tst where
  nd := 1
  nin := 0
  nout := 1
  body := .loop (.var 0) (.call .draw [] [] [⟨0, .var 1 + .var 2⟩])

/-- **The loop of scalar draws meets the contract of the vector draw**: the block receives the
window of `n` entries, in order. -/
theorem gaussLoopImpl_spec {I : Interp ROp Tst K}
    (hI : I.IsFn .total .draw (.draw Stream.gauss) AnyOperands)
    (adm : List ℕ → List (ℕ × ℕ) → List (ℕ × ℕ) → Prop) :
    (gaussLoopImpl (Tst := Tst)).Triple I .total ((drawRel Stream.gauss).spec adm) := by
  refine Impl.meets_rel fun d ins outs τ m xs hnd hadm hl hr _ hz => ?_
  obtain ⟨n, rfl⟩ := List.length_eq_one_iff.mp hnd
  obtain ⟨rfl, rfl⟩ := Mem.readBlocks_zero hr
  obtain ⟨z, rfl, hz'⟩ := Mem.room_one hz
  obtain ⟨S, p⟩ := m
  replace hz : z.2 + n ≤ S.len z.1 := hz'
  refine ⟨⟨rfl, rfl, rfl⟩, wp_loop_fill (b := z.1) (o := z.2)
    (fun i => τ (p + i) Stream.gauss) (fun i => p + i) rfl (fun i hi s' hfr _ => ?_) hz
    fun s' hfr hr' => ⟨[τ.window Stream.gauss p n], by simp [drawRel], rfl, ?_⟩⟩
  · exact wp_call_draw hI (z := (z.1, z.2 + i)) rfl rfl rfl trivial
      (by change z.2 + i < s'.len z.1; rw [hfr.len_eq]; omega) rfl
  · change (⟨s', p + n⟩ : Mem K) = ⟨S.updBlock z.1 z.2 (τ.window Stream.gauss p n), p + n⟩
    rw [hfr.eq_updBlock hr']
    rfl

/-- The table: `gauss` by the loop, every other operation kept. -/
def gaussTable : Table ROp ROp Tst
  | .gauss => .inl gaussLoopImpl
  | o => .inr o

/-- The cost: `n` scalar draws for a vector draw of length `n`. -/
noncomputable def gaussCost : ROp → List ℕ → Count ROp Tst
  | .gauss, d => d.headD 0 • Count.one .draw []
  | o, d => Count.one o d

/-- **The profile of the vector draw by scalar draws.** No scratch; the windows are those of the
catalog. -/
noncomputable def gaussLoop : Profile ROp ROp Tst where
  table := gaussTable
  cost := gaussCost
  ws _ _ := 0
  wsLo _ _ := 0
  win := randWindow
  winLo := randWindow

/-- **The certificate of the profile**: over the base contracts, the linked interpretation meets
them and the contract of the vector draw. -/
theorem gaussLoop_certifies [Inhabited K] (dec : K → ℝ) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) :
    (gaussLoop (Tst := Tst)).Refines (IsRandBase dec A) (IsRandLin dec A) := by
  refine .of_accounts (fun I hI => ?_) (fun I => Table.accounts_of_static ?_ ?_ I)
    fun I _ hloc o => ?_
  · exact
      { draw := Interp.link_meets_kept (o' := ROp.draw) rfl hI.draw
        matvec := Interp.link_meets_kept (o' := ROp.operator .matvec) rfl hI.matvec
        dot := Interp.link_meets_kept (o' := ROp.dot) rfl hI.dot
        add := Interp.link_meets_kept (o' := ROp.add) rfl hI.add
        nrm2 := Interp.link_meets_kept (o' := ROp.nrm2) rfl hI.nrm2
        mulc := fun q => Interp.link_meets_kept (o' := ROp.mulc q) rfl (hI.mulc q)
        axpy := Interp.link_meets_kept (o' := ROp.axpy) rfl hI.axpy
        gauss := Interp.link_meets (o := ROp.gauss) rfl (gaussLoopImpl_spec hI.draw _) }
  · intro o R hT d offs hd ho
    cases o <;> cases hT
    obtain ⟨k, rfl⟩ := List.length_eq_one_iff.mp hd
    obtain ⟨a, rfl⟩ := List.length_eq_one_iff.mp ho
    simp [gaussLoop, gaussLoopImpl, gaussCost, stmtCost, stmtPeak, useCost]
  · intro o o' hT d
    cases o <;> cases hT <;> simp [gaussLoop, gaussCost]
  · cases o
    case gauss =>
      exact Interp.TapeLocal.link hloc (o := ROp.gauss) rfl
        (by simp [Stmt.Straight, gaussLoopImpl]) fun d offs hd ho => by
          obtain ⟨k, rfl⟩ := List.length_eq_one_iff.mp hd
          obtain ⟨a, rfl⟩ := List.length_eq_one_iff.mp ho
          simp [staticWindow, gaussLoopImpl, gaussLoop, randWindow]
    all_goals exact Interp.TapeLocal.link_kept rfl (hloc _)

end NLAlib.Ops.Rand
