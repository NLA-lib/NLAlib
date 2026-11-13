/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Static

/-!
# Allocation-free statement bodies

The syntactic certificate below ignores operation identities and index values. An
allocation-free body needs no additional stored cells when primitive workspace is zero,
even when it contains bounded queries, loops, early exits, or nested frames.

## Main results

* `NLAlib.Ops.Stmt.allocationFree`: a decidable structural certificate.
* `NLAlib.Ops.stmtPeak_zero_of_allocationFree`: the corresponding exact workspace result.
-/

@[expose] public section

namespace NLAlib.Ops

variable {Op Tst : Type}

/-- A structural certificate that every branch contains no allocation instruction.
It makes no assertion about the workspace required by primitive operations. -/
def Stmt.allocationFree : Stmt Op Tst → Bool
  | .skip | .abort | .call .. => true
  | .seq s t | .ite _ _ _ s t | .whileFuel _ _ _ _ s t =>
      s.allocationFree && t.allocationFree
  | .bindIdx _ _ _ s | .loop _ s | .frame _ _ s => s.allocationFree
  | .allocAs .. => false

/-- With zero primitive workspace, a structurally allocation-free body has exactly zero
scratch, for every index environment, including environments where an expression fails. -/
theorem stmtPeak_zero_of_allocationFree {s : Stmt Op Tst}
    (h : s.allocationFree = true) (idx : List ℕ) :
    stmtPeak (fun _ _ => 0) s idx = 0 := by
  have hz (s : Finset ℕ) : (s.sup fun _ => (0 : ℕ)) = 0 := Finset.sup_bot s
  induction s generalizing idx with
  | skip | abort => rfl
  | call o ds ins outs =>
    simp only [stmtPeak]
    cases IExp.evalList idx ds <;> rfl
  | seq s t ihs iht | ite q ds args s t ihs iht =>
    obtain ⟨hs, ht⟩ := Bool.and_eq_true_iff.mp h
    simp only [stmtPeak, ihs hs, iht ht, max_self]
  | whileFuel fuel q ds args s t ihs iht =>
    obtain ⟨hs, ht⟩ := Bool.and_eq_true_iff.mp h
    simp only [stmtPeak, ihs hs, iht ht, hz, max_self]
  | bindIdx q args bound s ih =>
    simp only [stmtPeak, ih h, hz]
  | allocAs fmt len s ih => cases h
  | loop n s ih => simp only [stmtPeak, ih h, hz]
  | frame ds args s ih =>
    simp only [stmtPeak]
    cases IExp.evalList idx ds <;> cases IExp.evalList idx (args.map Operand.off) <;>
      simp only [ih h]

/-- A frame's operand evaluation cannot increase its workspace. A body estimate uniform
in operand offsets therefore needs only the actual evaluated dimension list. -/
theorem stmtPeak_frame_le {W : Op → List ℕ → ℕ} {ds : List IExp}
    {args : List Operand} {body : Stmt Op Tst} {idx d : List ℕ} {p : ℕ}
    (hd : IExp.evalList idx ds = some d)
    (hb : ∀ offs, stmtPeak W body (d ++ offs) ≤ p) :
    stmtPeak W (.frame ds args body) idx ≤ p := by
  simp only [stmtPeak, hd]
  cases IExp.evalList idx (args.map Operand.off) with
  | none => exact Nat.zero_le _
  | some offs => exact hb offs

/-- A uniform body workspace ceiling survives procedure framing, including invalid
dimensions or offsets, which contribute zero static workspace. -/
theorem stmtPeak_frame_le_uniform {W : Op → List ℕ → ℕ} {body : Stmt Op Tst} {p : ℕ}
    (h : ∀ idx, stmtPeak W body idx ≤ p)
    (ds : List IExp) (args : List Operand) (idx : List ℕ) :
    stmtPeak W (.frame ds args body) idx ≤ p := by
  cases hd : IExp.evalList idx ds with
  | none => simp [stmtPeak, hd]
  | some d => exact stmtPeak_frame_le hd (fun offs => h (d ++ offs))

/-- A frame body may also use the known number of operand offsets, for example to locate
a newly bound loop or query index after its dimensions and operands. -/
theorem stmtPeak_frame_le_of_length {W : Op → List ℕ → ℕ} {ds : List IExp}
    {args : List Operand} {body : Stmt Op Tst} {idx d : List ℕ} {p : ℕ}
    (hd : IExp.evalList idx ds = some d)
    (hb : ∀ offs, offs.length = args.length → stmtPeak W body (d ++ offs) ≤ p) :
    stmtPeak W (.frame ds args body) idx ≤ p := by
  simp only [stmtPeak, hd]
  cases he : IExp.evalList idx (args.map Operand.off) with
  | none => exact Nat.zero_le _
  | some offs =>
    apply hb offs
    simpa only [List.length_map] using (IExp.length_of_evalList he)

end NLAlib.Ops
