/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.LinearSystems.CGProgramRoundedInitialization

/-!
# Rounded initialization without stored matrix entries

The fixed oracle CG initializer executes the shared scalar and vector kernels. It loads
no matrix and assumes no initialized residual cache or numerical trajectory.

## Main results

* `NLAlib.CGOracleImplementation.exec_rounded_initialization`: actual initialized cache.
-/

@[expose] public section

namespace NLAlib.CGOracleImplementation

open Computation Computation.Builder CGImplementation
open scoped Matrix

variable {P ι K : Type} [DecidableEq P] {u : P → ℝ} {dec : P → K → ℝ}

/-- Actual scalar setup and vector initialization compose without a matrix load.
The supplied flag words require only their local literal, negation and decoding facts;
no global scalar arithmetic contract is needed. Input words are copied exactly. -/
theorem exec_rounded_setup (I : Interp P ι K (OpCount P ι)) (tag : P)
    (zero one negative : K) (hz : I.sem.lit tag 0 = some zero) (hd0 : dec tag zero = 0)
    (ho : I.sem.lit tag 1 = some one) (hpos : 0 < dec tag one)
    (herr : |dec tag one - 1| ≤ u tag) (hn : I.sem.un tag .neg one = some negative)
    (hdn : dec tag negative = -dec tag one)
    (hc : IsUnitCharge I)
    (st : St P K (OpCount P ι)) (N : ℕ) (b : Fin N → K)
    (hshape : st.store.shape = workspaceShape tag N false)
    (hb : ∀ i : Fin N, st.store.read tag 0 i = some (b i))
    :
    ∃ (out : St P K (OpCount P ι)) (zero one negative : K),
      exec I (do
        ins (.lit tag ⟨7, 6⟩ 0)
        ins (.lit tag ⟨7, 7⟩ 1)
        ins (.un tag .neg ⟨7, 8⟩ ⟨7, 7⟩)
        ins (.copy tag ⟨4, 0⟩ ⟨7, 6⟩)
        forRange (.const N) fun i => ins (.lit tag ⟨1, .var i⟩ 0)
        copyv tag 0 0 2 0 (.const N)
        copyv tag 0 0 3 0 (.const N)).run st = some out ∧
      out.store.shape = workspaceShape tag N false ∧
      (∀ i : Fin N, out.store.read tag 0 i = some (b i)) ∧
      (∀ i : Fin N, out.store.read tag 1 i = some zero) ∧
      (∀ i : Fin N, out.store.read tag 2 i = some (b i)) ∧
      (∀ i : Fin N, out.store.read tag 3 i = some (b i)) ∧
      out.store.read tag 7 6 = some zero ∧ out.store.read tag 7 7 = some one ∧
      out.store.read tag 7 8 = some negative ∧ out.store.read tag 4 0 = some zero ∧
      dec tag zero = 0 ∧ 0 < dec tag one ∧ |dec tag one - 1| ≤ u tag ∧
      dec tag negative = -dec tag one := by
  obtain ⟨pre, epre, shpre, rz, ro, rn, rs, fpre, _⟩ :=
    exec_cg_constant_words I tag zero one negative hz ho hn st
      (by simp [hshape, workspaceShape]) (by simp [hshape, workspaceShape])
  have rbpre (i : Fin N) : pre.store.read tag 0 i = some (b i) :=
    (fpre tag 0 i (by norm_num) (Or.inl (by norm_num))).trans (hb i)
  obtain ⟨out, evec, shvec, rx, rr, rp, fvec, _⟩ := exec_cg_vector_words I tag zero hz hc
    pre N b (by simp [shpre, hshape, workspaceShape])
      (by simp [shpre, hshape, workspaceShape])
      (by simp [shpre, hshape, workspaceShape]) rbpre
  have frame (buf idx : ℕ) (h1 : buf ≠ 1) (h2 : buf ≠ 2) (h3 : buf ≠ 3) :
      out.store.read tag buf idx = pre.store.read tag buf idx := fvec tag buf idx h1 h2 h3
  refine ⟨out, zero, one, negative, ?_, shvec.trans (shpre.trans hshape), ?_,
    rx, rr, rp, ?_, ?_, ?_, ?_, hd0, hpos, herr, hdn⟩
  · change exec I ((do
      ins (.lit tag ⟨7, 6⟩ 0); ins (.lit tag ⟨7, 7⟩ 1)
      ins (.un tag .neg ⟨7, 8⟩ ⟨7, 7⟩); ins (.copy tag ⟨4, 0⟩ ⟨7, 6⟩)) >>= fun _ => (do
        forRange (.const N) fun i => ins (.lit tag ⟨1, .var i⟩ 0)
        copyv tag 0 0 2 0 (.const N); copyv tag 0 0 3 0 (.const N))).run st = some out
    have ec : ExecutionComposable I (do
        ins (.lit tag ⟨7, 6⟩ 0); ins (.lit tag ⟨7, 7⟩ 1)
        ins (.un tag .neg ⟨7, 8⟩ ⟨7, 7⟩); ins (.copy tag ⟨4, 0⟩ ⟨7, 6⟩)) :=
      (executionComposable_single I (fun _ => rfl)).bind
        ((executionComposable_single I (fun _ => rfl)).bind
          ((executionComposable_single I (fun _ => rfl)).bind
            (executionComposable_single I (fun _ => rfl))))
    rw [ec, epre, Option.bind_some]
    exact evec
  · intro i
    rw [frame 0 _ (by norm_num) (by norm_num) (by norm_num)]
    exact rbpre i
  · exact (frame 7 6 (by norm_num) (by norm_num) (by norm_num)).trans rz
  · exact (frame 7 7 (by norm_num) (by norm_num) (by norm_num)).trans ro
  · exact (frame 7 8 (by norm_num) (by norm_num) (by norm_num)).trans rn
  · exact (frame 4 0 (by norm_num) (by norm_num) (by norm_num)).trans rs

/-- The complete actual initializer supplies the stored header and initial cache errors.
Empty input and empty dimension are included; literal-one positivity needs unit roundoff
below one independently of the dimension-dependent budget. The input is decoded from its
actual words; the matrix is supplied to the later oracle
contract. No desired numerical-state premise is used. -/
theorem exec_rounded_initialization (I : Interp P ι K (OpCount P ι)) (tag : P)
    (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem) (hz : AddsZeroExactly dec I.sem)
    (hu : u tag < 1) (hc : IsUnitCharge I)
    (st : St P K (OpCount P ι)) (N : ℕ) (b : Fin N → K) (A : Matrix (Fin N) (Fin N) ℝ)
    (hshape : st.store.shape = workspaceShape tag N false)
    (hb : ∀ i : Fin N, st.store.read tag 0 i = some (b i))
    (hsmall : cgImplementationRoundoffBound N (u tag) ≤ 1 / 100) :
    ∃ (predot cached header : St P K (OpCount P ι)) (ν θ flag : ℝ),
      exec I (do
        ins (.lit tag ⟨7, 6⟩ 0)
        ins (.lit tag ⟨7, 7⟩ 1)
        ins (.un tag .neg ⟨7, 8⟩ ⟨7, 7⟩)
        ins (.copy tag ⟨4, 0⟩ ⟨7, 6⟩)
        forRange (.const N) fun i => ins (.lit tag ⟨1, .var i⟩ 0)
        copyv tag 0 0 2 0 (.const N)
        copyv tag 0 0 3 0 (.const N)
        dot tag ⟨7, 0⟩ 2 0 2 0 (.const N)
        ifThenElse tag .eq ⟨7, 0⟩ ⟨7, 6⟩
          (ins (.copy tag ⟨4, 0⟩ ⟨7, 7⟩)) (pure ())).run st = some header ∧
      predot.store.shape = workspaceShape tag N false ∧
      (∀ i : Fin N, ∃ w, predot.store.read tag 2 i = some w ∧ dec tag w = dec tag (b i)) ∧
      exec I (dot tag ⟨7, 0⟩ 2 0 2 0 (.const N)).run predot = some cached ∧
      header.store.read tag 7 0 = cached.store.read tag 7 0 ∧
      StoreContext tag dec N A (fun i => dec tag (b i))
        ⟨0, fun i => dec tag (b i), fun i => dec tag (b i)⟩ ν
        (if (fun i : Fin N => dec tag (b i)) = 0 then flag else 0) flag header.store false ∧
      ν = ‖WithLp.toLp 2 (fun i : Fin N => dec tag (b i))‖ ^ 2 * (1 + θ) ∧
      |θ| ≤ cgImplementationRoundoffBound N (u tag) ∧ 0 ≤ ν ∧
      (ν = 0 ↔ (fun i : Fin N => dec tag (b i)) = 0) ∧
      0 < flag ∧ |flag - 1| ≤ u tag := by
  classical
  obtain ⟨zeroWord, oneWord, negativeWord, hz0, hdz, ho, hpos0, herr, hn, hdn0⟩ :=
    exists_cg_flag_words I tag ((hsem.isArithErrSem (fun _ => trivial)).lit_zero tag)
      (by
        obtain ⟨one, ho⟩ := hsem.lit_ok tag 1 trivial
        exact ⟨one, ho, by simpa only [RelErr, Rat.cast_one] using hsem.lit_err tag 1 one ho⟩)
      (hsem.neg tag) hu
  obtain ⟨predot, zero, one, negative, epre, sh, rb, rx, rr, rp, rz, ro, rn,
      rs, hd0, hpos, hflag, hdn⟩ := exec_rounded_setup I tag zeroWord oneWord negativeWord
        hz0 hdz ho hpos0 herr hn hdn0 hc st N b hshape hb
  have hread (i : Fin N) :
      ∃ w, predot.store.read tag 2 i = some w ∧ dec tag w = dec tag (b i) := ⟨b i, rr i, rfl⟩
  obtain ⟨scratch, hw⟩ := Store.exists_write_eq_some_of_getElem?_shape zero
    (show predot.store.shape[7]? = some (tag, 9) by simp [sh, workspaceShape])
    (show 0 < 9 by norm_num)
  obtain ⟨cached, w, θ, edot, write, heq, hθ, hnonneg, hzero⟩ :=
    exec_rounded_initial_pairing I tag hsem hz predot N (fun i => dec tag (b i)) hsmall
      hread ⟨zero, scratch, hw⟩
  have ctx := storeContext_of_pairing_write tag N predot.store cached.store b
    A zero one negative w sh trivial rb rx rr rp rz ro rn rs hd0 hdn write
  obtain ⟨header, estop, hout, frame⟩ := exec_rounded_stop_guard I tag hsem cached N
    A (fun i => dec tag (b i))
    ⟨0, fun i => dec tag (b i), fun i => dec tag (b i)⟩ (dec tag w) 0 (dec tag one) ctx
  refine ⟨predot, cached, header, dec tag w, θ, dec tag one, ?_, sh, hread,
    edot, frame tag 7 0 (by norm_num), ?_, heq, hθ, hnonneg, hzero, hpos, hflag⟩
  · change exec I ((do
      ins (.lit tag ⟨7, 6⟩ 0); ins (.lit tag ⟨7, 7⟩ 1)
      ins (.un tag .neg ⟨7, 8⟩ ⟨7, 7⟩); ins (.copy tag ⟨4, 0⟩ ⟨7, 6⟩)) >>= fun _ => (do
        forRange (.const N) fun i => ins (.lit tag ⟨1, .var i⟩ 0)
        copyv tag 0 0 2 0 (.const N); copyv tag 0 0 3 0 (.const N)) >>= fun _ => (do
          dot tag ⟨7, 0⟩ 2 0 2 0 (.const N)
          ifThenElse tag .eq ⟨7, 0⟩ ⟨7, 6⟩
            (ins (.copy tag ⟨4, 0⟩ ⟨7, 7⟩)) (pure ()))).run st = some header
    rw [← bind_assoc]
    have ec : ExecutionComposable I (do
        ins (.lit tag ⟨7, 6⟩ 0); ins (.lit tag ⟨7, 7⟩ 1)
        ins (.un tag .neg ⟨7, 8⟩ ⟨7, 7⟩); ins (.copy tag ⟨4, 0⟩ ⟨7, 6⟩)) :=
      (executionComposable_single I (fun _ => rfl)).bind
        ((executionComposable_single I (fun _ => rfl)).bind
          ((executionComposable_single I (fun _ => rfl)).bind
            (executionComposable_single I (fun _ => rfl))))
    rw [ec.bind (executionComposable_rounded_vectors I tag N)]
    simp only [bind_assoc]
    rw [epre, Option.bind_some, exec_run_bind I
        (b := dot tag ⟨7, 0⟩ 2 0 2 0 (.const N)) (fun _ => rfl), edot, Option.bind_some]
    exact estop
  · simpa only [hzero] using hout

end NLAlib.CGOracleImplementation
