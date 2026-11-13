/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.LinearSystems.CGProgramInitialization
public import NLAlib.Krylov.LinearSystems.CGProgramLoop
public import NLAlib.Krylov.LinearSystems.CGProgramScope

/-!
# Outer realization of the approved stored CG target

Concrete initial-store and allocation bookkeeping for the approved canonical program.
Private state abbreviations describe existing `St` records and their actual allocation
updates; they add no arithmetic or algorithm interface. The target theorem is assembled from
actual initialization and loop executions.

## Main results

* `NLAlib.storedEntriesConjugateGradient`: the approved exact stored-entries target,
  including guarded success for all real inputs, conditional SPD correspondence,
  componentwise operation bounds and peak memory including ROM.
-/

@[expose] public section

namespace NLAlib.CGImplementation

open Computation Computation.Builder
open scoped Matrix

variable {P ι : Type} [DecidableEq P]

private def workspaceState (tag : P) (N : ℕ) (b : Fin N → ℝ) : St P ℝ (OpCount P ι) where
  store := #[(tag, (Array.ofFn b).map some), (tag, Array.replicate N none),
    (tag, Array.replicate N none), (tag, Array.replicate N none),
    (tag, Array.replicate 1 none), (tag, Array.replicate (N * N) none),
    (tag, Array.replicate N none), (tag, Array.replicate 9 none)]
  pos _ := 0
  cnt := 0
  cur q := if q = tag then N * N + 5 * N + 10 else 0
  peak q := if q = tag then N * N + 5 * N + 10 else 0
  curW := 0
  peakW := 0

private theorem workspaceState_shape (tag : P) (N : ℕ) (b : Fin N → ℝ) :
    (workspaceState (ι := ι) tag N b).store.shape = workspaceShape tag N := by
  simp [workspaceState, workspaceShape, Store.shape]

private theorem workspaceState_read (tag : P) (N : ℕ) (b : Fin N → ℝ) (i : Fin N) :
    (workspaceState (ι := ι) tag N b).store.read tag 0 i = some (b i) := by
  simp [workspaceState, Store.read, i.isLt]

private theorem allocationState_eq_workspace (tag : P) (N : ℕ) (b : Fin N → ℝ) :
    (let st0 := declaredState (C := OpCount P ι) tag N b
     let st1 := { st0 with
       store := st0.store.push (tag, Array.replicate (N * N) none)
       cur := Function.update st0.cur tag (st0.cur tag + N * N)
       peak := Function.update st0.peak tag (max (st0.peak tag) (st0.cur tag + N * N))
       curW := st0.curW + (N * N) * 0
       peakW := max st0.peakW (st0.curW + (N * N) * 0) }
     let st2 := { st1 with
       store := st1.store.push (tag, Array.replicate N none)
       cur := Function.update st1.cur tag (st1.cur tag + N)
       peak := Function.update st1.peak tag (max (st1.peak tag) (st1.cur tag + N))
       curW := st1.curW + N * 0
       peakW := max st1.peakW (st1.curW + N * 0) }
     { st2 with
       store := st2.store.push (tag, Array.replicate 9 none)
       cur := Function.update st2.cur tag (st2.cur tag + 9)
       peak := Function.update st2.peak tag (max (st2.peak tag) (st2.cur tag + 9))
       curW := st2.curW + 9 * 0
       peakW := max st2.peakW (st2.curW + 9 * 0) }) = workspaceState tag N b := by
  dsimp only [declaredState, workspaceState, inputState]
  congr 1
  · funext q
    by_cases hq : q = tag <;> simp [hq]
    omega
  · funext q
    by_cases hq : q = tag <;> simp [hq]
    omega

private def releasedState (tag : P) (N : ℕ) (out : St P ℝ (OpCount P ι)) :
    St P ℝ (OpCount P ι) := { out with
  store := out.store.pop.pop.pop
  cur := Function.update out.cur tag (out.cur tag - 9 - N - N * N) }

private theorem exec_cg_allocations (I : Interp P ι ℝ (OpCount P ι))
    (tag : P) (N : ℕ) (b : Fin N → ℝ) (hw : I.width tag = 0)
    (body : ℕ → ℕ → ℕ → Builder P ι ℕ ℕ Unit) (out : St P ℝ (OpCount P ι))
    (hbody : exec I (body 5 6 7).run (workspaceState tag N b) = some out) :
    exec I (scope do
      let A ← alloc tag (IExp.const N * IExp.const N)
      let s ← alloc tag (IExp.const N)
      let scalars ← alloc tag 9
      body A s scalars).run (declaredState tag N b) = some (releasedState tag N out) := by
  change exec I (.seq (.alloc tag (IExp.const N * IExp.const N) fun A =>
    .alloc tag (IExp.const N) fun s => .alloc tag 9 fun scalars => (body A s scalars).run)
      .skip) (declaredState tag N b) = _
  rw [exec_seq_skip, exec_alloc, exec_alloc, exec_alloc]
  have hsize : (declaredState (C := OpCount P ι) tag N b).store.size = 5 := by
    simp [declaredState, inputState]
  simp only [IExp.eval_mul, IExp.eval_const, IExp.eval_ofNat, hw, Array.size_push,
    hsize, Nat.reduceAdd]
  rw [allocationState_eq_workspace, hbody]
  simp only [Option.map_some, mul_zero, Nat.sub_zero, Function.update_self,
    Function.update_idem, releasedState]

private theorem exec_cg_workspace_bind (I : Interp P ι ℝ (OpCount P ι))
    (tag : P) (N q : ℕ) (st : St P ℝ (OpCount P ι)) :
    exec I (do
      forRange ((IExp.const N) * (IExp.const N)) fun i => stmt (.rom tag ⟨5, .var i⟩ (.var i))
      ins (.lit tag ⟨7, 6⟩ 0)
      ins (.lit tag ⟨7, 7⟩ 1)
      ins (.un tag .neg ⟨7, 8⟩ ⟨7, 7⟩)
      ins (.copy tag ⟨4, 0⟩ ⟨7, 6⟩)
      forRange (IExp.const N) fun i => ins (.lit tag ⟨1, .var i⟩ 0)
      copyv tag 0 0 2 0 (IExp.const N)
      copyv tag 0 0 3 0 (IExp.const N)
      dot tag ⟨7, 0⟩ 2 0 2 0 (IExp.const N)
      ifThenElse tag .eq ⟨7, 0⟩ ⟨7, 6⟩
        (ins (.copy tag ⟨4, 0⟩ ⟨7, 7⟩)) (pure ())
      forRange (IExp.const q) fun _ => ifThenElse tag .eq ⟨4, 0⟩ ⟨7, 6⟩
        (do
          gemv tag (IExp.const N) (IExp.const N) 5 0 3 0 6 0
          dot tag ⟨7, 2⟩ 3 0 6 0 (IExp.const N)
          ifThenElse tag .lt ⟨7, 6⟩ ⟨7, 2⟩ (do
            ins (.bin tag .div ⟨7, 3⟩ ⟨7, 0⟩ ⟨7, 2⟩)
            axpy tag ⟨7, 3⟩ 3 0 1 0 (IExp.const N)
            ins (.un tag .neg ⟨7, 5⟩ ⟨7, 3⟩)
            axpy tag ⟨7, 5⟩ 6 0 2 0 (IExp.const N)
            dot tag ⟨7, 1⟩ 2 0 2 0 (IExp.const N)
            ins (.bin tag .div ⟨7, 4⟩ ⟨7, 1⟩ ⟨7, 0⟩)
            forRange (IExp.const N) fun i => do
              ins (.bin tag .mul ⟨7, 2⟩ ⟨7, 4⟩ ⟨3, .var i⟩)
              ins (.bin tag .add ⟨3, .var i⟩ ⟨2, .var i⟩ ⟨7, 2⟩)
            ins (.copy tag ⟨7, 0⟩ ⟨7, 1⟩)
            ifThenElse tag .eq ⟨7, 0⟩ ⟨7, 6⟩
              (ins (.copy tag ⟨4, 0⟩ ⟨7, 7⟩)) (pure ()))
            (ins (.copy tag ⟨4, 0⟩ ⟨7, 8⟩))) (pure ())).run st = (exec I (do
      forRange ((IExp.const N) * (IExp.const N)) fun i => stmt (.rom tag ⟨5, .var i⟩ (.var i))
      ins (.lit tag ⟨7, 6⟩ 0)
      ins (.lit tag ⟨7, 7⟩ 1)
      ins (.un tag .neg ⟨7, 8⟩ ⟨7, 7⟩)
      ins (.copy tag ⟨4, 0⟩ ⟨7, 6⟩)
      forRange (IExp.const N) fun i => ins (.lit tag ⟨1, .var i⟩ 0)
      copyv tag 0 0 2 0 (IExp.const N)
      copyv tag 0 0 3 0 (IExp.const N)
      dot tag ⟨7, 0⟩ 2 0 2 0 (IExp.const N)
      ifThenElse tag .eq ⟨7, 0⟩ ⟨7, 6⟩
        (ins (.copy tag ⟨4, 0⟩ ⟨7, 7⟩)) (pure ())).run st).bind
        (exec I (forRange (IExp.const q) fun _ => ifThenElse tag .eq ⟨4, 0⟩ ⟨7, 6⟩
    (do
      gemv tag (IExp.const N) (IExp.const N) 5 0 3 0 6 0
      dot tag ⟨7, 2⟩ 3 0 6 0 (IExp.const N)
      ifThenElse tag .lt ⟨7, 6⟩ ⟨7, 2⟩ (do
        ins (.bin tag .div ⟨7, 3⟩ ⟨7, 0⟩ ⟨7, 2⟩)
        axpy tag ⟨7, 3⟩ 3 0 1 0 (IExp.const N)
        ins (.un tag .neg ⟨7, 5⟩ ⟨7, 3⟩)
        axpy tag ⟨7, 5⟩ 6 0 2 0 (IExp.const N)
        dot tag ⟨7, 1⟩ 2 0 2 0 (IExp.const N)
        ins (.bin tag .div ⟨7, 4⟩ ⟨7, 1⟩ ⟨7, 0⟩)
        forRange (IExp.const N) fun i => do
          ins (.bin tag .mul ⟨7, 2⟩ ⟨7, 4⟩ ⟨3, .var i⟩)
          ins (.bin tag .add ⟨3, .var i⟩ ⟨2, .var i⟩ ⟨7, 2⟩)
        ins (.copy tag ⟨7, 0⟩ ⟨7, 1⟩)
        ifThenElse tag .eq ⟨7, 0⟩ ⟨7, 6⟩
          (ins (.copy tag ⟨4, 0⟩ ⟨7, 7⟩)) (pure ()))
        (ins (.copy tag ⟨4, 0⟩ ⟨7, 8⟩))) (pure ())).run) := by
  exact executionComposable_cg_initialization I tag N (fun _ =>
forRange (IExp.const q) fun _ => ifThenElse tag .eq ⟨4, 0⟩ ⟨7, 6⟩
      (do
        gemv tag (IExp.const N) (IExp.const N) 5 0 3 0 6 0
        dot tag ⟨7, 2⟩ 3 0 6 0 (IExp.const N)
        ifThenElse tag .lt ⟨7, 6⟩ ⟨7, 2⟩ (do
          ins (.bin tag .div ⟨7, 3⟩ ⟨7, 0⟩ ⟨7, 2⟩)
          axpy tag ⟨7, 3⟩ 3 0 1 0 (IExp.const N)
          ins (.un tag .neg ⟨7, 5⟩ ⟨7, 3⟩)
          axpy tag ⟨7, 5⟩ 6 0 2 0 (IExp.const N)
          dot tag ⟨7, 1⟩ 2 0 2 0 (IExp.const N)
          ins (.bin tag .div ⟨7, 4⟩ ⟨7, 1⟩ ⟨7, 0⟩)
          forRange (IExp.const N) fun i => do
            ins (.bin tag .mul ⟨7, 2⟩ ⟨7, 4⟩ ⟨3, .var i⟩)
            ins (.bin tag .add ⟨3, .var i⟩ ⟨2, .var i⟩ ⟨7, 2⟩)
          ins (.copy tag ⟨7, 0⟩ ⟨7, 1⟩)
          ifThenElse tag .eq ⟨7, 0⟩ ⟨7, 6⟩
            (ins (.copy tag ⟨4, 0⟩ ⟨7, 7⟩)) (pure ()))
          (ins (.copy tag ⟨4, 0⟩ ⟨7, 8⟩))) (pure ())) st

open scoped Classical in
private theorem exec_cg_workspace_body (I : Interp P ι ℝ (OpCount P ι))
    (hI : I.sem = exactSem) (hc : IsUnitCharge I)
    (tag : P) (N q : ℕ) (b : Fin N → ℝ) (vals : ℕ → ℝ)
    (hw : I.width tag = 0) (hrom : ∀ i < N * N, I.rom i = some (vals i)) :
    ∃ out v status, exec I (do
      forRange ((IExp.const N) * (IExp.const N)) fun i => stmt (.rom tag ⟨5, .var i⟩ (.var i))
      ins (.lit tag ⟨7, 6⟩ 0)
      ins (.lit tag ⟨7, 7⟩ 1)
      ins (.un tag .neg ⟨7, 8⟩ ⟨7, 7⟩)
      ins (.copy tag ⟨4, 0⟩ ⟨7, 6⟩)
      forRange (IExp.const N) fun i => ins (.lit tag ⟨1, .var i⟩ 0)
      copyv tag 0 0 2 0 (IExp.const N)
      copyv tag 0 0 3 0 (IExp.const N)
      dot tag ⟨7, 0⟩ 2 0 2 0 (IExp.const N)
      ifThenElse tag .eq ⟨7, 0⟩ ⟨7, 6⟩
        (ins (.copy tag ⟨4, 0⟩ ⟨7, 7⟩)) (pure ())
      forRange (IExp.const q) fun _ => ifThenElse tag .eq ⟨4, 0⟩ ⟨7, 6⟩
        (do
          gemv tag (IExp.const N) (IExp.const N) 5 0 3 0 6 0
          dot tag ⟨7, 2⟩ 3 0 6 0 (IExp.const N)
          ifThenElse tag .lt ⟨7, 6⟩ ⟨7, 2⟩ (do
            ins (.bin tag .div ⟨7, 3⟩ ⟨7, 0⟩ ⟨7, 2⟩)
            axpy tag ⟨7, 3⟩ 3 0 1 0 (IExp.const N)
            ins (.un tag .neg ⟨7, 5⟩ ⟨7, 3⟩)
            axpy tag ⟨7, 5⟩ 6 0 2 0 (IExp.const N)
            dot tag ⟨7, 1⟩ 2 0 2 0 (IExp.const N)
            ins (.bin tag .div ⟨7, 4⟩ ⟨7, 1⟩ ⟨7, 0⟩)
            forRange (IExp.const N) fun i => do
              ins (.bin tag .mul ⟨7, 2⟩ ⟨7, 4⟩ ⟨3, .var i⟩)
              ins (.bin tag .add ⟨3, .var i⟩ ⟨2, .var i⟩ ⟨7, 2⟩)
            ins (.copy tag ⟨7, 0⟩ ⟨7, 1⟩)
            ifThenElse tag .eq ⟨7, 0⟩ ⟨7, 6⟩
              (ins (.copy tag ⟨4, 0⟩ ⟨7, 7⟩)) (pure ()))
            (ins (.copy tag ⟨4, 0⟩ ⟨7, 8⟩))) (pure ())).run (workspaceState tag N b) = some out ∧
      StoreContext tag (fun _ x => x) N (fun i j => vals (i + N * j)) b v
        (v.r ⬝ᵥ v.r) status 1 out.store ∧
      (status = 0 ∨ status = 1 ∨ status = -1) ∧
      (Matrix.PosDef (fun (i j : Fin N) => vals (i + N * j)) →
        v = cgState (fun (i j : Fin N) => vals (i + N * j)) b 0 q ∧
          (status = 1 ↔ v.r = 0) ∧ status ≠ -1) ∧
      out.pos = (workspaceState (ι := ι) tag N b).pos ∧
      out.cur = (workspaceState (ι := ι) tag N b).cur ∧
      out.curW = 0 ∧ out.cnt ≤ cgCount tag N q ∧
      (∀ p, out.peak p ≤ if p = tag then N * N + 5 * N + 11 else 0) ∧ out.peakW = 0 := by
  obtain ⟨ini, eini, sh, inp, mat, hx, hr, hp, hnu, hz, ho, hn, hs, _, pos, cur,
      curW, cnt, peak, peakW⟩ := exec_cg_initialization I hI hc tag
    (workspaceState tag N b) N b vals (by
      simpa [workspaceShape] using workspaceState_shape (ι := ι) tag N b)
    (workspaceState_read tag N b) hrom
  have ctx : StoreContext tag (fun _ x => x) N (fun i j => vals (i + N * j)) b
      ⟨0, b, b⟩ (b ⬝ᵥ b) (if b = 0 then 1 else 0) 1 ini.store := by
    refine ⟨sh.trans (workspaceState_shape tag N b), ?_, ?_, ?_, ?_, ?_,
      ⟨_, hnu, rfl⟩, ⟨_, hs, rfl⟩, ⟨_, hz, rfl⟩, ⟨_, ho, rfl⟩, ⟨_, hn, rfl⟩⟩
    · intro i j; exact ⟨_, mat i j, rfl⟩
    · intro i; exact ⟨_, inp i, rfl⟩
    · intro i; exact ⟨_, hx i, rfl⟩
    · intro i; exact ⟨_, hr i, rfl⟩
    · intro i; exact ⟨_, hp i, rfl⟩
  obtain ⟨out, v, status, eloop, ctx', allowed, exactv, pos', cur', curW', cnt', peak', peakW'⟩ :=
    exec_exact_loop I hI hc tag ini N q (fun i j => vals (i + N * j)) b ctx
  refine ⟨out, v, status, ?_, ctx', allowed, exactv, pos'.trans pos, cur'.trans cur,
    curW'.trans curW, ?_, ?_, ?_⟩
  · rw [exec_cg_workspace_bind, eini, Option.bind_some]
    exact eloop
  · calc
      out.cnt ≤ ini.cnt + q • stepCount tag N := cnt'
      _ ≤ (0 + cgCount tag N 0) + q • stepCount tag N :=
        add_le_add cnt le_rfl
      _ = cgCount tag N q := by rw [zero_add, cgCount_decompose]
  · intro p
    have h := peak' p
    rw [peak, cur] at h
    by_cases hpt : p = tag
    · subst p
      simp only [Function.update_self] at h
      simp [workspaceState] at h ⊢
      omega
    · simpa [workspaceState, hpt] using h
  · have h := peakW'
    rw [peakW, curW, hw] at h
    simpa only [workspaceState, zero_add, max_self, Nat.le_zero] using h

private theorem post_released (tag : P) (N q : ℕ) (A : Matrix (Fin N) (Fin N) ℝ)
    (b : Fin N → ℝ) (out : St P ℝ (OpCount P ι)) (v : CGState ℝ (Fin N)) (status : ℝ)
    (ctx : StoreContext tag (fun _ x => x) N A b v (v.r ⬝ᵥ v.r) status 1 out.store)
    (allowed : status = 0 ∨ status = 1 ∨ status = -1)
    (exactv : A.PosDef → v = cgState A b 0 q ∧ (status = 1 ↔ v.r = 0) ∧ status ≠ -1) :
    ∃ status : ℝ, (releasedState tag N out).store.read tag 4 0 = some status ∧
      (status = 0 ∨ status = 1 ∨ status = -1) ∧
      Holds (releasedState tag N out).store tag 0 0 (fun i (_ : Fin 1) => b i) ∧
      (A.PosDef →
        Holds (releasedState tag N out).store tag 1 0
          (fun i (_ : Fin 1) => (cgState A b 0 q).x i) ∧
        Holds (releasedState tag N out).store tag 2 0
          (fun i (_ : Fin 1) => (cgState A b 0 q).r i) ∧
        Holds (releasedState tag N out).store tag 3 0
          (fun i (_ : Fin 1) => (cgState A b 0 q).p i) ∧
        (status = 1 ↔ (cgState A b 0 q).r = 0) ∧ status ≠ -1) := by
  have hsize : out.store.size = 8 := by rw [← Store.size_shape, ctx.shape]; rfl
  have popread (q : P) (buf i : ℕ) (hbuf : buf < 5) :
      (releasedState tag N out).store.read q buf i = out.store.read q buf i := by
    change Store.read out.store.pop.pop.pop q buf i = _
    rw [Store.read_pop_of_lt (by simpa only [Array.size_pop, hsize] using hbuf),
      Store.read_pop_of_lt (by simp only [Array.size_pop, hsize]; omega),
      Store.read_pop_of_lt (by rw [hsize]; omega)]
  have holds (buf : ℕ) (hbuf : buf < 5) (x : Fin N → ℝ)
      (hx : ∀ i : Fin N, ∃ w, out.store.read tag buf i = some w ∧ w = x i) :
      Holds (releasedState tag N out).store tag buf 0 (fun i (_ : Fin 1) => x i) := by
    intro i j
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    simp only [Fin.val_zero, mul_zero, add_zero, zero_add]
    rw [popread tag buf i hbuf]
    obtain ⟨w, hw, hval⟩ := hx i
    simpa only [hval] using hw
  refine ⟨status, ?_, allowed, holds 0 (by omega) b ctx.input, ?_⟩
  · rw [popread tag 4 0 (by omega)]
    obtain ⟨w, hw, hval⟩ := ctx.statusValue
    simpa only [hval] using hw
  · intro hA
    obtain ⟨hv, hterm, hneg⟩ := exactv hA
    subst v
    exact ⟨holds 1 (by omega) _ ctx.iterate, holds 2 (by omega) _ ctx.residual,
      holds 3 (by omega) _ ctx.direction, hterm, hneg⟩

private theorem exec_cg_program (I : Interp P ι ℝ (OpCount P ι))
    (hI : I.sem = exactSem) (hc : IsUnitCharge I)
    (tag : P) (N q : ℕ) (b : Fin N → ℝ) (vals : ℕ → ℝ)
    (hw : I.width tag = 0) (hrom : ∀ i < N * N, I.rom i = some (vals i)) :
    ∃ final, exec I (cgProg tag (IExp.const N) (IExp.const q) 0 1 2 3 4).run
        (declaredState tag N b) = some final ∧ final.cnt ≤ cgCount tag N q ∧
      (∀ p, final.peak p ≤ if p = tag then N * N + 5 * N + 11 else 0) ∧
      ∃ status : ℝ, final.store.read tag 4 0 = some status ∧
        (status = 0 ∨ status = 1 ∨ status = -1) ∧
        Holds final.store tag 0 0 (fun i (_ : Fin 1) => b i) ∧
        (Matrix.PosDef (fun (i j : Fin N) => vals (i + N * j)) →
          Holds final.store tag 1 0
            (fun i (_ : Fin 1) => (cgState (fun (i j : Fin N) => vals (i + N * j)) b 0 q).x i) ∧
          Holds final.store tag 2 0
            (fun i (_ : Fin 1) => (cgState (fun (i j : Fin N) => vals (i + N * j)) b 0 q).r i) ∧
          Holds final.store tag 3 0
            (fun i (_ : Fin 1) => (cgState (fun (i j : Fin N) => vals (i + N * j)) b 0 q).p i) ∧
          (status = 1 ↔ (cgState (fun (i j : Fin N) => vals (i + N * j)) b 0 q).r = 0) ∧
          status ≠ -1) := by
  let body : ℕ → ℕ → ℕ → Builder P ι ℕ ℕ Unit := fun A s scalars => do
    forRange ((IExp.const N) * (IExp.const N)) fun i => stmt (.rom tag ⟨A, .var i⟩ (.var i))
    ins (.lit tag ⟨scalars, 6⟩ 0)
    ins (.lit tag ⟨scalars, 7⟩ 1)
    ins (.un tag .neg ⟨scalars, 8⟩ ⟨scalars, 7⟩)
    ins (.copy tag ⟨4, 0⟩ ⟨scalars, 6⟩)
    forRange (IExp.const N) fun i => ins (.lit tag ⟨1, .var i⟩ 0)
    copyv tag 0 0 2 0 (IExp.const N)
    copyv tag 0 0 3 0 (IExp.const N)
    dot tag ⟨scalars, 0⟩ 2 0 2 0 (IExp.const N)
    ifThenElse tag .eq ⟨scalars, 0⟩ ⟨scalars, 6⟩
      (ins (.copy tag ⟨4, 0⟩ ⟨scalars, 7⟩)) (pure ())
    forRange (IExp.const q) fun _ => ifThenElse tag .eq ⟨4, 0⟩ ⟨scalars, 6⟩
      (do
        gemv tag (IExp.const N) (IExp.const N) A 0 3 0 s 0
        dot tag ⟨scalars, 2⟩ 3 0 s 0 (IExp.const N)
        ifThenElse tag .lt ⟨scalars, 6⟩ ⟨scalars, 2⟩ (do
          ins (.bin tag .div ⟨scalars, 3⟩ ⟨scalars, 0⟩ ⟨scalars, 2⟩)
          axpy tag ⟨scalars, 3⟩ 3 0 1 0 (IExp.const N)
          ins (.un tag .neg ⟨scalars, 5⟩ ⟨scalars, 3⟩)
          axpy tag ⟨scalars, 5⟩ s 0 2 0 (IExp.const N)
          dot tag ⟨scalars, 1⟩ 2 0 2 0 (IExp.const N)
          ins (.bin tag .div ⟨scalars, 4⟩ ⟨scalars, 1⟩ ⟨scalars, 0⟩)
          forRange (IExp.const N) fun i => do
            ins (.bin tag .mul ⟨scalars, 2⟩ ⟨scalars, 4⟩ ⟨3, .var i⟩)
            ins (.bin tag .add ⟨3, .var i⟩ ⟨2, .var i⟩ ⟨scalars, 2⟩)
          ins (.copy tag ⟨scalars, 0⟩ ⟨scalars, 1⟩)
          ifThenElse tag .eq ⟨scalars, 0⟩ ⟨scalars, 6⟩
            (ins (.copy tag ⟨4, 0⟩ ⟨scalars, 7⟩)) (pure ()))
          (ins (.copy tag ⟨4, 0⟩ ⟨scalars, 8⟩))) (pure ())
  obtain ⟨out, v, status, ebody, ctx, allowed, exactv, _, _, _, cnt, peak, _⟩ :=
    exec_cg_workspace_body I hI hc tag N q b vals hw hrom
  have ealloc := exec_cg_allocations I tag N b hw body out ebody
  refine ⟨releasedState tag N out, ?_, cnt, peak, ?_⟩
  · simpa only [cgProg, body] using ealloc
  · exact post_released tag N q _ b out v status ctx allowed exactv

end NLAlib.CGImplementation

namespace NLAlib

open Computation

/-- **Stored conjugate gradients.** For all dimensions $N$ and requested step counts $q$,
including zero, the registered tree runs under exact real arithmetic on every column-major ROM
matrix $\mathbf{A}$ and declared right-hand side $\mathbf{b}$, from zero iterate and
uninitialized output cells. The program $\mathsf{cgProg}(\mathbf{A},\mathbf{b},q)$ preserves
its input and returns iterate, residual, direction and status. A zero residual stops active
steps; nonpositive curvature returns negative status before division. Status $0$ means budget
exhaustion, $1$ zero-residual termination and $-1$ nonpositive curvature.

For positive definite $\mathbf{A}$, the three returned vectors equal the Hestenes–Stiefel CG
state after $q$ steps, padded after zero termination, positive status is equivalent to a zero
final residual, and negative status is excluded. The recurrence is
[HestenesStiefel1952, (3:1)]; the guards and storage specify the registered implementation.

Componentwise upper counts are $N^2$ ROM reads, $N+q(N^2+5N)$ multiplications and additions,
$N+2qN$ conjugations, $2q$ divisions, $q+1$ negations, $N+3+q(N+2)$ literals, $1+3q$ comparisons
and $2N+2q+2$ copies; all other operation counts vanish. Peak memory, including ROM, declared
buffers and scratch, is at most $2N^2+5N+11$ scalar cells at the arithmetic tag and zero at
other tags. These are exact-arithmetic program guarantees, with no floating-point contract.

Result: cg-program -/
theorem storedEntriesConjugateGradient : StoredEntriesConjugateGradient := by
  intro P ι inst tag N n _ b vals ξ
  let I : Interp P ι ℝ (OpCount P ι) := storedInterp (N ^ 2) vals ξ tag
  have hn : n = ![n 0] := by
    funext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    rfl
  obtain ⟨out, hrun, hcnt, hpeak, hpost⟩ :=
    CGImplementation.exec_cg_program I rfl (fun _ => rfl) tag N (n 0) b vals rfl
      (fun i hi => by
        change (if i < N ^ 2 then some (vals i) else none) = some (vals i)
        exact if_pos (by simpa only [pow_two] using hi))
  refine ⟨by simp, out, ?_, ?_, ?_, hpost⟩
  · rw [Prog.exec_eq_exec_toStmt, hn, cgProg.toStmt_compiled]
    exact hrun
  · simpa only [inputState, zero_add] using hcnt
  · intro p
    have h := hpeak p
    by_cases hp : p = tag
    · subst p
      have h' : out.peak tag ≤ N * N + 5 * N + 11 := by simpa using h
      change out.peak tag + (if tag = tag then N ^ 2 else 0) ≤
        if tag = tag then 2 * N ^ 2 + 5 * N + 11 else 0
      simp only [ite_true, pow_two]
      omega
    · change out.peak p + (if p = tag then N ^ 2 else 0) ≤
        if p = tag then 2 * N ^ 2 + 5 * N + 11 else 0
      simpa only [if_neg hp, add_zero] using h

/-- **The conjugate-gradient target is not vacuous**
(`docs/design/Computation-Hardening.md`, §2.2): for every $N_0$ there are tags and oracle names
(`Unit`) and sizes $N = N_0 + 1$, $n = (1)$ (no size condition), the declared input type
$\mathbb{R}^N$ inhabited (by the zero vector). The witness of
`NLAlib.StoredEntriesConjugateGradient` (`scripts/Targets.lean`, item 7). No printed source. -/
theorem storedEntriesConjugateGradient_nonVacuous : ∀ N₀ : ℕ,
    ∃ (P ι : Type) (_ : DecidableEq P) (tag : P),
    StoredEntries.NonVacuous (𝕜 := ℝ) tag (cgProg.compiled (ι := ι) tag)
      (fun _ _ => True) (fun N _ => Fin N → ℝ)
      (fun N _ b => ![(Array.ofFn b).map some, Array.replicate N none,
        Array.replicate N none, Array.replicate N none, Array.replicate 1 none])
      (fun N _ => N ^ 2) (fun N q => cgCount tag N (q 0))
      (fun N _ p => if p = tag then 2 * N ^ 2 + 5 * N + 11 else 0)
      (fun N q b vals _ st =>
        let A : Matrix (Fin N) (Fin N) ℝ := fun i j => vals (i + N * j)
        ∃ status : ℝ, st.store.read tag 4 0 = some status ∧
          (status = 0 ∨ status = 1 ∨ status = -1) ∧
          Holds st.store tag 0 0 (fun i (_ : Fin 1) => b i) ∧
          (A.PosDef →
            Holds st.store tag 1 0 (fun i (_ : Fin 1) => (cgState A b 0 (q 0)).x i) ∧
            Holds st.store tag 2 0 (fun i (_ : Fin 1) => (cgState A b 0 (q 0)).r i) ∧
            Holds st.store tag 3 0 (fun i (_ : Fin 1) => (cgState A b 0 (q 0)).p i) ∧
            (status = 1 ↔ (cgState A b 0 (q 0)).r = 0) ∧ status ≠ -1)) N₀ :=
  fun N₀ => ⟨Unit, Unit, inferInstance, (), N₀ + 1, fun _ => 1, Nat.le_succ N₀, trivial,
    ⟨0⟩⟩

end NLAlib
