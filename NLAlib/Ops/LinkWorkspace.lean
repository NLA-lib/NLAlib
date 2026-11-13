/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Link
public import NLAlib.Ops.Workspace

/-!
# Independent stored workspace through fixed implementation tables

A table whose implementations reserve at most a common number of stored cells adds
that reservation only once to the source program's allocation peak. Calls are sequential;
loops and alternative control-flow branches therefore do not multiply this reservation.

## Main results

* `NLAlib.Ops.stmtPeak_link_le_zero_add` is the shared stored-workspace linking bound.
-/

@[expose] public section

namespace NLAlib.Ops

variable {Op Lo Tst : Type}

private theorem peak_link_call_le (T : Table Op Lo Tst) (w : ℕ)
    (hT : ∀ o r, T o = .inl r → ∀ idx, stmtPeak (fun _ _ => 0) r.body idx ≤ w)
    (o : Op) (ds : List IExp) (ins outs : List Operand) (idx : List ℕ) :
    stmtPeak (fun (_ : Lo) _ => 0) ((Stmt.call o ds ins outs).link T) idx ≤ w := by
  cases ht : T o with
  | inl r =>
    by_cases hf : r.Fits ds.length ins.length outs.length
    · simp only [Stmt.link, ht, if_pos hf, stmtPeak]
      cases IExp.evalList idx ds <;>
        cases IExp.evalList idx ((ins ++ outs).map Operand.off) <;>
        first | exact Nat.zero_le _ | exact hT o r ht _
    · simp [Stmt.link, ht, hf, stmtPeak]
  | inr o' =>
    simp only [Stmt.link, ht, stmtPeak]
    cases IExp.evalList idx ds <;> simp

/-- A fixed table with uniform stored scratch adds one shared reservation above the source
allocation peak. The bound also covers invalid arities and unevaluable expressions, whose
linked calls abort. It assumes no successful execution or algorithm-specific invariant. -/
theorem stmtPeak_link_le_zero_add (T : Table Op Lo Tst) (w : ℕ)
    (hT : ∀ o r, T o = .inl r → ∀ idx, stmtPeak (fun _ _ => 0) r.body idx ≤ w)
    (s : Stmt Op Tst) (idx : List ℕ) :
    stmtPeak (fun (_ : Lo) _ => 0) (s.link T) idx ≤
      stmtPeak (fun (_ : Op) _ => 0) s idx + w := by
  have hsup (t : Finset ℕ) (f g : ℕ → ℕ)
      (h : ∀ i ∈ t, f i ≤ g i + w) : t.sup f ≤ t.sup g + w := by
    apply Finset.sup_le
    intro i hi
    exact (h i hi).trans (Nat.add_le_add_right (Finset.le_sup hi) w)
  induction s generalizing idx with
  | skip | abort => exact Nat.zero_le _
  | call o ds ins outs =>
    have h := peak_link_call_le T w hT o ds ins outs idx
    cases he : IExp.evalList idx ds <;> simpa [stmtPeak, he] using h
  | seq s t ihs iht | ite q ds args s t ihs iht =>
    change max _ _ ≤ max _ _ + w
    exact max_le ((ihs idx).trans (Nat.add_le_add_right (Nat.le_max_left ..) w))
      ((iht idx).trans (Nat.add_le_add_right (Nat.le_max_right ..) w))
  | whileFuel fuel q ds args s t ihs iht =>
    change max _ _ ≤ max _ _ + w
    refine max_le ((hsup _ _ _ fun i _ => ihs (idx ++ [i])).trans
      (Nat.add_le_add_right (Nat.le_max_left ..) w)) ?_
    exact (hsup _ _ _ fun i _ => iht (idx ++ [i])).trans
      (Nat.add_le_add_right (Nat.le_max_right ..) w)
  | bindIdx q args bound s ih | loop bound s ih =>
    exact hsup _ _ _ fun i _ => ih (idx ++ [i])
  | allocAs fmt len s ih =>
    simpa only [Stmt.link, stmtPeak, Nat.add_assoc] using
      Nat.add_le_add_left (ih idx) (fmt.bytes * (len.eval idx).getD 0)
  | frame ds args s ih =>
    simp only [Stmt.link, stmtPeak]
    cases IExp.evalList idx ds <;> cases IExp.evalList idx (args.map Operand.off) <;>
      first | exact Nat.zero_le _ | exact ih _

end NLAlib.Ops
