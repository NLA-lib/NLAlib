/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.ShiftedQR.Step
public import NLAlib.Ops.Logic.Loop

/-!
# Stored sequences of exact shifted QR steps

Each round executes the actual scalar shifted-step program into a temporary matrix and
copies its words back to the input/output matrix. The scratch matrix is allocated once for
the complete sequence. Shift words are protected throughout the computation.

## Main results

* `NLAlib.ShiftedQR.stepInPlaceWithScratch`: one actual shifted step and scalar copy-back.
* `NLAlib.ShiftedQR.repeatedStep`: repeat one supplied complex shift a finite number of times.
* `NLAlib.ShiftedQR.multiStep`: execute a stored finite column of complex shifts.
* `NLAlib.ShiftedQR.repeatedStep_writes`: total repeated mathematical shifted QR.
* `NLAlib.ShiftedQR.multiStep_writes`: total mathematical composition of the actual shift list.
-/

@[expose] public section

namespace NLAlib.ShiftedQR

open Ops

variable {Op Tst : Type} [Has ScalarOp Op] [Has CmpTst Tst]

/-- One exact shifted step with a caller-owned temporary matrix and exactly aliased output. -/
def stepInPlaceWithScratch : Impl Op Tst := opsImpl% [n] (A, S, T) → (A) {
  run shiftedStep.body [n] (A, S, T);
  run (unaryMap (Has.inj ScalarOp.copy)).body [2 * (n * n)] (T, A)
}

/-- Repeat one stored complex shift, retaining the matrix in its exactly aliased view. -/
def repeatedStepWithScratch : Impl Op Tst := opsImpl% [n, k] (A, S, T) → (A) {
  for j < k {
    run stepInPlaceWithScratch.body [n] (A, S, T, A)
  }
}

/-- Repeated shifted QR allocates one temporary matrix for the complete finite loop. -/
def repeatedStep : Impl Op Tst := opsImpl% [n, k] (A, S) → (A) {
  let T ← alloc (2 * (n * n));
  run repeatedStepWithScratch.body [n, k] (A, S, T, A)
}

/-- Apply a stored column of `k` complex shifts, in its physical order. -/
def multiStepWithScratch : Impl Op Tst := opsImpl% [n, k] (A, S, T) → (A) {
  for j < k {
    run stepInPlaceWithScratch.body [n] (A, S[2 * j], T, A)
  }
}

/-- A finite list of stored shifts shares one matrix scratch allocation across all steps. -/
def multiStep : Impl Op Tst := opsImpl% [n, k] (A, S) → (A) {
  let T ← alloc (2 * (n * n));
  run multiStepWithScratch.body [n, k] (A, S, T, A)
}

/-- One actual shifted step followed by scalar copy-back computes the mathematical shifted
step in place. The temporary matrix and supplied shift are spatially disjoint from outputs. -/
theorem stepInPlaceWithScratch_writes {M : Machine ℝ} {I : Interp Op Tst ℝ}
    (hS : IsScalar M I) (hE : ExactModel id M) (hCmp : IsCmp id I)
    {τ : Tape ℝ} {m : Mem ℝ} {n : ℕ} {a s t : ℕ × ℕ}
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {shift : ℂ}
    (hl : m.Live [a, s, t]) (hH : HoldsMatrix a H m.store)
    (hs : m.store.readBlock s.1 s.2 2 = some [shift.re, shift.im])
    (ht : t.2 + 2 * ((n + 1) * (n + 1)) ≤ m.store.len t.1)
    (hat : Fp.Disj (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))))
      (Store.inBlock t.1 t.2 (2 * ((n + 1) * (n + 1)))))
    (hst : Fp.Disj (Store.inBlock s.1 s.2 2)
      (Store.inBlock t.1 t.2 (2 * ((n + 1) * (n + 1))))) :
    Writes .total I τ stepInPlaceWithScratch.body (Env.frame [n + 1] [a, s, t, a])
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔
        Store.inBlock t.1 t.2 (2 * ((n + 1) * (n + 1))))
      (fun μ => μ.pos = m.pos ∧ HoldsMatrix a (shiftedQRStep H shift) μ.store) m := by
  have hlive : a.1 < m.store.length ∧ s.1 < m.store.length ∧ t.1 < m.store.length := by
    simpa only [Mem.Live, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] using hl
  have ha := Store.le_len_of_readBlock hH (by positivity)
  have hstep := shiftedStep_writes (τ := τ) hS hE hCmp hl hH hs ht hat hst
  refine hstep.frame_seq_le rfl rfl hl le_sup_right ?_
  intro m₁ hfr ⟨hp, hT⟩
  have hcopy := copyMatrix_writes (τ := τ) hS hT (by rw [hfr.len_eq]; exact ha) hat.symm
  refine (hcopy.in_frame rfl rfl (by simp only [Mem.Live, List.mem_cons,
    List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; rw [hfr.length_eq]; omega)).mono
    le_sup_left ?_
  intro m₂ _ ⟨hp₂, hA⟩
  exact ⟨hp₂.trans hp, hA⟩

private theorem multiShiftedQRStep_replicate {n : ℕ}
    (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (shift : ℂ) (k : ℕ) :
    multiShiftedQRStep H (List.replicate k shift) = (fun B => shiftedQRStep B shift)^[k] H := by
  induction k generalizing H with
  | zero => rfl
  | succ k ih =>
    simpa only [multiShiftedQRStep, List.replicate_succ, List.foldl_cons,
      Function.iterate_succ_apply] using ih (shiftedQRStep H shift)

/-- Repeating a supplied shift composes the actual in-place step exactly `k` times. No
convergence, pivot, or successful-execution hypothesis is used. -/
theorem repeatedStepWithScratch_writes {M : Machine ℝ} {I : Interp Op Tst ℝ}
    (hS : IsScalar M I) (hE : ExactModel id M) (hCmp : IsCmp id I)
    {τ : Tape ℝ} {m : Mem ℝ} {n k : ℕ} {a s t : ℕ × ℕ}
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {shift : ℂ}
    (hl : m.Live [a, s, t, a]) (hH : HoldsMatrix a H m.store)
    (hs : m.store.readBlock s.1 s.2 2 = some [shift.re, shift.im])
    (ht : t.2 + 2 * ((n + 1) * (n + 1)) ≤ m.store.len t.1)
    (hat : Fp.Disj (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))))
      (Store.inBlock t.1 t.2 (2 * ((n + 1) * (n + 1)))))
    (hsa : Fp.Disj (Store.inBlock s.1 s.2 2)
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1)))))
    (hst : Fp.Disj (Store.inBlock s.1 s.2 2)
      (Store.inBlock t.1 t.2 (2 * ((n + 1) * (n + 1))))) :
    Writes .total I τ repeatedStepWithScratch.body (Env.frame [n + 1, k] [a, s, t, a])
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔
        Store.inBlock t.1 t.2 (2 * ((n + 1) * (n + 1))))
      (fun μ => μ.pos = m.pos ∧
        HoldsMatrix a (multiShiftedQRStep H (List.replicate k shift)) μ.store) m := by
  have hloop := writes_loop_frame_iterate
    (State := fun B μ => HoldsMatrix a B μ.store)
    (transition := fun B => shiftedQRStep B shift) (valid := fun _ => True)
    (s := H) (n := .var 1) (N := k) (md := .total) (I := I) (τ := τ)
    (ρ := Env.frame [n + 1, k] [a, s, t, a])
    (body := stepInPlaceWithScratch.body) (ds := [.var 0])
    (args := [⟨0, .var 2⟩, ⟨1, .var 3⟩, ⟨2, .var 4⟩, ⟨0, .var 2⟩])
    (F := Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔
      Store.inBlock t.1 t.2 (2 * ((n + 1) * (n + 1))))
    rfl rfl rfl hl hH (fun _ _ => trivial) ?_
  · simpa only [repeatedStepWithScratch, multiShiftedQRStep_replicate] using hloop
  · intro B μ hfr hlive hB _
    have hs' := hfr.keep (Store.readsOnly_readBlock _ _ _ _)
      (Fp.disj_sup_left.mpr ⟨hsa.symm, hst.symm⟩) hs
    exact stepInPlaceWithScratch_writes hS hE hCmp
      (by simpa [Mem.Live, and_assoc, and_left_comm, and_comm] using hlive) hB hs'
      (by rw [hfr.len_eq]; exact ht) hat hst


private theorem multiShiftedQRStep_take_succ {n : ℕ}
    (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (ss : List ℂ) (i : ℕ) (hi : i < ss.length) :
    multiShiftedQRStep H (ss.take (i + 1)) =
      shiftedQRStep (multiShiftedQRStep H (ss.take i)) ss[i] := by
  have ht : ss.take (i + 1) = ss.take i ++ [ss[i]] := by
    rw [List.take_add_one, List.getElem?_eq_getElem hi]
    rfl
  simp only [multiShiftedQRStep, ht, List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- A stored finite shift column composes exactly the mathematical list of shifted QR steps.
The matrix temporary is reused across the entire list. -/
theorem multiStepWithScratch_writes {M : Machine ℝ} {I : Interp Op Tst ℝ}
    (hS : IsScalar M I) (hE : ExactModel id M) (hCmp : IsCmp id I)
    {τ : Tape ℝ} {m : Mem ℝ} {n : ℕ} {a s t : ℕ × ℕ} {ss : List ℂ}
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hl : m.Live [a, s, t, a]) (hH : HoldsMatrix a H m.store)
    (hSS : HoldsMatrix s (shiftColumn ss) m.store)
    (ht : t.2 + 2 * ((n + 1) * (n + 1)) ≤ m.store.len t.1)
    (hat : Fp.Disj (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))))
      (Store.inBlock t.1 t.2 (2 * ((n + 1) * (n + 1)))))
    (hsa : Fp.Disj (Store.inBlock s.1 s.2 (2 * ss.length))
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1)))))
    (hst : Fp.Disj (Store.inBlock s.1 s.2 (2 * ss.length))
      (Store.inBlock t.1 t.2 (2 * ((n + 1) * (n + 1))))) :
    Writes .total I τ multiStepWithScratch.body
      (Env.frame [n + 1, ss.length] [a, s, t, a])
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔
        Store.inBlock t.1 t.2 (2 * ((n + 1) * (n + 1))))
      (fun μ => μ.pos = m.pos ∧ HoldsMatrix a (multiShiftedQRStep H ss) μ.store) m := by
  let F := Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔
    Store.inBlock t.1 t.2 (2 * ((n + 1) * (n + 1)))
  refine (writes_loop (n := .var 1) (N := ss.length) rfl (fun _ => F) (fun _ _ => le_rfl)
    (fun i μ => μ.pos = m.pos ∧ HoldsMatrix a (multiShiftedQRStep H (ss.take i)) μ.store)
    ⟨rfl, by simpa only [List.take_zero, multiShiftedQRStep, List.foldl_nil] using hH⟩
    ?_).mono le_rfl ?_
  · intro i hi μ hfr ⟨hp, hA⟩
    have hSS' := hSS.of_eqOff hfr (by
      simpa only [F, Nat.one_mul] using Fp.disj_sup_left.mpr ⟨hsa.symm, hst.symm⟩)
    have hs' : μ.store.readBlock s.1 (s.2 + 2 * i) 2 = some [(ss[i]).re, (ss[i]).im] := by
      simpa only [shiftColumn, Fin.val_zero, Nat.zero_mul, Nat.zero_add, Fin.getElem_fin] using
        hSS'.read_entry ⟨i, hi⟩ (0 : Fin 1)
    have hst' : Fp.Disj (Store.inBlock s.1 (s.2 + 2 * i) 2)
        (Store.inBlock t.1 t.2 (2 * ((n + 1) * (n + 1)))) := by
      refine hst.mono ?_ le_rfl
      intro b j hj
      exact ⟨hj.1, by have := hj.2.1; omega, by have := hj.2.2; omega⟩
    have hstep := stepInPlaceWithScratch_writes (τ := τ) (s := (s.1, s.2 + 2 * i)) hS hE hCmp
      (by simpa [Mem.Live, hfr.length_eq, and_assoc, and_left_comm, and_comm] using hl) hA hs'
      (by rw [hfr.len_eq]; exact ht) hat hst'
    refine (hstep.in_frame rfl rfl (by
      simpa [Mem.Live, hfr.length_eq, and_assoc, and_left_comm, and_comm] using hl)).mono
      le_rfl ?_
    intro μ' _ ⟨hp', hA'⟩
    exact ⟨hp'.trans hp, by simpa only [multiShiftedQRStep_take_succ H ss i hi] using hA'⟩
  · intro μ _ hp
    simpa only [List.take_length] using hp


/-- The scoped repeated-shift program returns the exact repeated mathematical QR step in
its original matrix view and releases its one temporary matrix. -/
theorem repeatedStep_writes {M : Machine ℝ} {I : Interp Op Tst ℝ}
    (hS : IsScalar M I) (hE : ExactModel id M) (hCmp : IsCmp id I)
    {τ : Tape ℝ} {m : Mem ℝ} {n k : ℕ} {a s : ℕ × ℕ}
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {shift : ℂ}
    (hl : m.Live [a, s, a]) (hH : HoldsMatrix a H m.store)
    (hs : m.store.readBlock s.1 s.2 2 = some [shift.re, shift.im])
    (hsa : Fp.Disj (Store.inBlock s.1 s.2 2)
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))))) :
    Writes .total I τ repeatedStep.body (Env.frame [n + 1, k] [a, s, a])
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))))
      (fun μ => μ.pos = m.pos ∧
        HoldsMatrix a (multiShiftedQRStep H (List.replicate k shift)) μ.store) m := by
  have hlive : a.1 < m.store.length ∧ s.1 < m.store.length := by
    simpa [Mem.Live, and_assoc, and_left_comm, and_comm] using hl
  change Writes .total I τ (Stmt.allocs [.const 2 * (.var 0 * .var 0)] _) _ _ _ m
  refine writes_allocs_preserving_post rfl
    (fun hBelow hp => ⟨hp.1, hp.2.of_below hBelow hlive.1⟩) ?_
  intro store hlen hlens hBelow
  let t : ℕ × ℕ := (m.store.length, 0)
  have ht : store.len t.1 = 2 * ((n + 1) * (n + 1)) := by
    simpa [t] using hlens 0 (by simp)
  have hat : Fp.Disj (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))))
      (Store.inBlock t.1 t.2 (2 * ((n + 1) * (n + 1)))) :=
    Fp.disj_inBlock_of_ne (by dsimp [t]; omega)
  have hst : Fp.Disj (Store.inBlock s.1 s.2 2)
      (Store.inBlock t.1 t.2 (2 * ((n + 1) * (n + 1)))) :=
    Fp.disj_inBlock_of_ne (by dsimp [t]; omega)
  have hbody := repeatedStepWithScratch_writes (k := k) (τ := τ) (m := ⟨store, m.pos⟩)
    hS hE hCmp (by simp [Mem.Live, t, hlen]; omega)
    (hH.of_below hBelow hlive.1) ((hBelow.readBlock hlive.2 _ _).trans hs)
    (by dsimp [t]; simpa only [Nat.zero_add] using ht.ge) hat hsa hst
  exact (hbody.in_frame rfl rfl (by simp [Mem.Live, t, hlen]; omega)).mono
    (sup_le le_sup_left (Fp.inBlock_le_sup_above (by dsimp [t]; omega)))
    (fun _ _ hp => hp)

/-- The scoped finite-list program returns the mathematical multi-shifted QR matrix and
releases the single temporary matrix used by every round. -/
theorem multiStep_writes {M : Machine ℝ} {I : Interp Op Tst ℝ}
    (hS : IsScalar M I) (hE : ExactModel id M) (hCmp : IsCmp id I)
    {τ : Tape ℝ} {m : Mem ℝ} {n : ℕ} {a s : ℕ × ℕ} {ss : List ℂ}
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hl : m.Live [a, s, a]) (hH : HoldsMatrix a H m.store)
    (hSS : HoldsMatrix s (shiftColumn ss) m.store)
    (hsa : Fp.Disj (Store.inBlock s.1 s.2 (2 * ss.length))
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))))) :
    Writes .total I τ multiStep.body (Env.frame [n + 1, ss.length] [a, s, a])
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))))
      (fun μ => μ.pos = m.pos ∧ HoldsMatrix a (multiShiftedQRStep H ss) μ.store) m := by
  have hlive : a.1 < m.store.length ∧ s.1 < m.store.length := by
    simpa [Mem.Live, and_assoc, and_left_comm, and_comm] using hl
  change Writes .total I τ (Stmt.allocs [.const 2 * (.var 0 * .var 0)] _) _ _ _ m
  refine writes_allocs_preserving_post rfl
    (fun hBelow hp => ⟨hp.1, hp.2.of_below hBelow hlive.1⟩) ?_
  intro store hlen hlens hBelow
  let t : ℕ × ℕ := (m.store.length, 0)
  have ht : store.len t.1 = 2 * ((n + 1) * (n + 1)) := by
    simpa [t] using hlens 0 (by simp)
  have hat : Fp.Disj (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))))
      (Store.inBlock t.1 t.2 (2 * ((n + 1) * (n + 1)))) :=
    Fp.disj_inBlock_of_ne (by dsimp [t]; omega)
  have hst : Fp.Disj (Store.inBlock s.1 s.2 (2 * ss.length))
      (Store.inBlock t.1 t.2 (2 * ((n + 1) * (n + 1)))) :=
    Fp.disj_inBlock_of_ne (by dsimp [t]; omega)
  have hbody := multiStepWithScratch_writes (τ := τ) (m := ⟨store, m.pos⟩)
    hS hE hCmp (by simp [Mem.Live, t, hlen]; omega)
    (hH.of_below hBelow hlive.1) (hSS.of_below hBelow hlive.2)
    (by dsimp [t]; simpa only [Nat.zero_add] using ht.ge) hat hsa hst
  exact (hbody.in_frame rfl rfl (by simp [Mem.Live, t, hlen]; omega)).mono
    (sup_le le_sup_left (Fp.inBlock_le_sup_above (by dsimp [t]; omega)))
    (fun _ _ hp => hp)


end NLAlib.ShiftedQR
