/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.LinearSystems.CGOracleProgramExecution
public import NLAlib.Krylov.LinearSystems.CGProgramInitialization

/-!
# Initialization of the oracle CG program

The actual scalar setup, zero iterate, input copies, cached self-dot and status test use the
canonical checked phases. No matrix ROM load is performed or assumed.

## Main results

* `NLAlib.CGOracleImplementation.exec_initialize`: actual oracle-program initialization.
-/

@[expose] public section

namespace NLAlib.CGOracleImplementation

open Computation Computation.Builder CGImplementation
open scoped Matrix

variable {P ι : Type} [DecidableEq P]

private theorem composable_constants (I : Interp P ι ℝ (OpCount P ι)) (tag : P) :
    ExecutionComposable I (do
      ins (.lit tag ⟨7, 6⟩ 0)
      ins (.lit tag ⟨7, 7⟩ 1)
      ins (.un tag .neg ⟨7, 8⟩ ⟨7, 7⟩)
      ins (.copy tag ⟨4, 0⟩ ⟨7, 6⟩)) :=
  (executionComposable_single I (b := ins (.lit tag ⟨7, 6⟩ 0)) (fun _ => rfl)).bind
    ((executionComposable_single I (b := ins (.lit tag ⟨7, 7⟩ 1)) (fun _ => rfl)).bind
      ((executionComposable_single I (b := ins (.un tag .neg ⟨7, 8⟩ ⟨7, 7⟩))
        (fun _ => rfl)).bind
        (executionComposable_single I (b := ins (.copy tag ⟨4, 0⟩ ⟨7, 6⟩)) (fun _ => rfl))))

/-- Initialization executes the scalar constants, zero iterate, two input copies, self-dot
and zero-residual test in the fixed order, for every real input including zero dimension. -/
theorem exec_initialize (I : Interp P ι ℝ (OpCount P ι)) (hI : I.sem = exactSem)
    (hc : IsUnitCharge I) (tag : P) (N : ℕ)
    (A : Matrix (Fin N) (Fin N) ℝ) (b : Fin N → ℝ) (st : St P ℝ (OpCount P ι))
    (hshape : st.store.shape = workspaceShape tag N false)
    (hb : ∀ i : Fin N, st.store.read tag 0 i = some (b i)) :
    ∃ out, exec I (do
      ins (.lit tag ⟨7, 6⟩ 0)
      ins (.lit tag ⟨7, 7⟩ 1)
      ins (.un tag .neg ⟨7, 8⟩ ⟨7, 7⟩)
      ins (.copy tag ⟨4, 0⟩ ⟨7, 6⟩)
      forRange (.const N) fun i => ins (.lit tag ⟨1, .var i⟩ 0)
      copyv tag 0 0 2 0 (.const N)
      copyv tag 0 0 3 0 (.const N)
      dot tag ⟨7, 0⟩ 2 0 2 0 (.const N)
      ifThenElse tag .eq ⟨7, 0⟩ ⟨7, 6⟩
        (ins (.copy tag ⟨4, 0⟩ ⟨7, 7⟩)) (pure ())).run st = some out ∧
      StoreContext tag (fun _ x => x) N A b ⟨0, b, b⟩ (b ⬝ᵥ b)
        (if b = 0 then 1 else 0) 1 out.store false ∧
      out.pos = st.pos ∧ out.cur = st.cur ∧ out.curW = st.curW := by
  classical
  obtain ⟨c, ec, sc, rz, ro, rn, rs, fc, state⟩ :=
    exec_cg_constants I hI tag st (by simp [hshape, workspaceShape])
      (by simp [hshape, workspaceShape])
  have shapeC := sc.trans hshape
  obtain ⟨v, ev, sv, rx, rr, rp, fv, pv, cv, wv, _, _, _⟩ :=
    exec_cg_vectors I hI hc tag c N b (by simp [shapeC, workspaceShape])
      (by simp [shapeC, workspaceShape]) (by simp [shapeC, workspaceShape])
      (fun i => (fc tag 0 i (by norm_num) (Or.inl (by norm_num))).trans (hb i))
  have shapeV := sv.trans shapeC
  have fr (i : ℕ) := fv tag 7 i (by norm_num) (by norm_num) (by norm_num)
  have fs := fv tag 4 0 (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨out, eo, so, rν, rstatus, fo, po, co, wo, _, _, _⟩ :=
    exec_cg_cache_status I hI hc tag v N b (by simp [shapeV, workspaceShape])
      (by simp [shapeV, workspaceShape]) rr ((fr 6).trans rz) ((fr 7).trans ro) (fs.trans rs)
  have pc : c.pos = st.pos := by simpa only using congrArg St.pos state
  have cc : c.cur = st.cur := by simpa only using congrArg St.cur state
  have wc : c.curW = st.curW := by simpa only using congrArg St.curW state
  refine ⟨out, ?_, ?_, po.trans (pv.trans pc), co.trans (cv.trans cc), wo.trans (wv.trans wc)⟩
  · change exec I ((do
      ins (.lit tag ⟨7, 6⟩ 0)
      ins (.lit tag ⟨7, 7⟩ 1)
      ins (.un tag .neg ⟨7, 8⟩ ⟨7, 7⟩)
      ins (.copy tag ⟨4, 0⟩ ⟨7, 6⟩)) >>= fun _ => (do
      forRange (.const N) fun i => ins (.lit tag ⟨1, .var i⟩ 0)
      copyv tag 0 0 2 0 (.const N)
      copyv tag 0 0 3 0 (.const N)) >>= fun _ => do
      dot tag ⟨7, 0⟩ 2 0 2 0 (.const N)
      ifThenElse tag .eq ⟨7, 0⟩ ⟨7, 6⟩
        (ins (.copy tag ⟨4, 0⟩ ⟨7, 7⟩)) (pure ())).run st = some out
    rw [composable_constants I tag, ec, Option.bind_some, executionComposable_cg_vectors I tag N,
      ev, Option.bind_some]
    exact eo
  · refine ⟨so.trans shapeV, trivial, ?_, ?_, ?_, ?_, ⟨_, rν, rfl⟩,
      ⟨_, rstatus, rfl⟩, ?_, ?_, ?_⟩
    · intro i
      exact ⟨b i, (fo tag 0 i (Or.inl (by norm_num)) (Or.inl (by norm_num))).trans
        ((fv tag 0 i (by norm_num) (by norm_num) (by norm_num)).trans
          ((fc tag 0 i (by norm_num) (Or.inl (by norm_num))).trans (hb i))), rfl⟩
    · intro i
      exact ⟨0, (fo tag 1 i (Or.inl (by norm_num)) (Or.inl (by norm_num))).trans (rx i), rfl⟩
    · intro i
      exact ⟨b i, (fo tag 2 i (Or.inl (by norm_num)) (Or.inl (by norm_num))).trans (rr i), rfl⟩
    · intro i
      exact ⟨b i, (fo tag 3 i (Or.inl (by norm_num)) (Or.inl (by norm_num))).trans (rp i), rfl⟩
    · exact ⟨0, (fo tag 7 6 (Or.inl (by norm_num)) (Or.inr (by norm_num))).trans
        ((fr 6).trans rz), rfl⟩
    · exact ⟨1, (fo tag 7 7 (Or.inl (by norm_num)) (Or.inr (by norm_num))).trans
        ((fr 7).trans ro), rfl⟩
    · exact ⟨-1, (fo tag 7 8 (Or.inl (by norm_num)) (Or.inr (by norm_num))).trans
        ((fr 8).trans rn), rfl⟩

/-- The actual initializer composes with the following requested-step loop. -/
theorem executionComposable_initialize (I : Interp P ι ℝ (OpCount P ι))
    (tag : P) (N : ℕ) : ExecutionComposable I (do
      ins (.lit tag ⟨7, 6⟩ 0)
      ins (.lit tag ⟨7, 7⟩ 1)
      ins (.un tag .neg ⟨7, 8⟩ ⟨7, 7⟩)
      ins (.copy tag ⟨4, 0⟩ ⟨7, 6⟩)
      forRange (.const N) fun i => ins (.lit tag ⟨1, .var i⟩ 0)
      copyv tag 0 0 2 0 (.const N)
      copyv tag 0 0 3 0 (.const N)
      dot tag ⟨7, 0⟩ 2 0 2 0 (.const N)
      ifThenElse tag .eq ⟨7, 0⟩ ⟨7, 6⟩
        (ins (.copy tag ⟨4, 0⟩ ⟨7, 7⟩)) (pure ())) :=
  (composable_constants I tag).bind ((executionComposable_cg_vectors I tag N).bind
    ((executionComposable_single I (b := dot tag ⟨7, 0⟩ 2 0 2 0 (.const N))
      (fun _ => rfl)).bind
      (executionComposable_single I (b := ifThenElse tag .eq ⟨7, 0⟩ ⟨7, 6⟩
        (ins (.copy tag ⟨4, 0⟩ ⟨7, 7⟩)) (pure ())) (fun _ => rfl))))

end NLAlib.CGOracleImplementation
