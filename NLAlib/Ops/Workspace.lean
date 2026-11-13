/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.CallSupport

/-!
# Separating stored allocations from primitive workspace

Only one primitive runs at a time. A common ceiling on primitive workspace is therefore
added once to the peak due to explicit allocations, regardless of loop counts and nesting.

## Main results

* `NLAlib.Ops.stmtPeak_le_zero_add`: shared primitive workspace above stored allocation peak.
* `NLAlib.Ops.stmtPeak_le_zero_add_on_support`: a ceiling only on supported call shapes.
-/

@[expose] public section

namespace NLAlib.Ops

variable {Op Tst : Type}

/-- A workspace ceiling restricted to the supported primitive calls. -/
abbrev Count.BoundsWorkspace (c : Count Op Tst) (W : Op → List ℕ → ℕ) (w : ℕ) : Prop :=
  c.CallsSatisfy (fun o ds => W o ds ≤ w)

/-- Only shapes in the static call support contribute primitive workspace. Shapes whose
index expressions fail to evaluate have neither a static call nor workspace. -/
theorem stmtPeak_le_zero_add_on_support (W : Op → List ℕ → ℕ) (w : ℕ)
    (s : Stmt Op Tst) (idx : List ℕ) (hW : (stmtCost s idx).BoundsWorkspace W w) :
    stmtPeak W s idx ≤ stmtPeak (fun _ _ => 0) s idx + w := by
  have hsup (t : Finset ℕ) (f g : ℕ → ℕ)
      (h : ∀ i ∈ t, f i ≤ g i + w) : t.sup f ≤ t.sup g + w := by
    apply Finset.sup_le
    intro i hi
    exact (h i hi).trans (Nat.add_le_add_right (Finset.le_sup hi) w)
  induction s generalizing idx with
  | skip | abort => exact Nat.zero_le _
  | call o ds ins outs =>
    cases he : IExp.evalList idx ds with
    | none => simp [stmtPeak, he]
    | some d =>
      have hb := hW o d (by simp [stmtCost, useCost, he, Count.one])
      simpa [stmtPeak, he] using hb
  | seq s t ihs iht =>
    apply max_le
    · exact (ihs idx (hW.mono le_self_add)).trans
        (Nat.add_le_add_right (Nat.le_max_left ..) w)
    · exact (iht idx (hW.mono le_add_self)).trans
        (Nat.add_le_add_right (Nat.le_max_right ..) w)
  | ite q ds args s t ihs iht =>
    apply max_le
    · exact (ihs idx (hW.mono ((le_sup_left).trans le_add_self))).trans
        (Nat.add_le_add_right (Nat.le_max_left ..) w)
    · exact (iht idx (hW.mono ((le_sup_right).trans le_add_self))).trans
        (Nat.add_le_add_right (Nat.le_max_right ..) w)
  | whileFuel fuel q ds args s t ihs iht =>
    apply max_le
    · apply (hsup _ _ _ ?_).trans (Nat.add_le_add_right (Nat.le_max_left ..) w)
      intro i hi
      apply ihs
      apply hW.mono
      have hc : stmtCost s (idx ++ [i]) ≤
          testCost q ds (idx ++ [i]) + stmtCost s (idx ++ [i]) := le_add_self
      have hs := Finset.single_le_sum
        (f := fun j => testCost q ds (idx ++ [j]) + stmtCost s (idx ++ [j]))
        (fun _ _ => (zero_le : (0 : Count Op Tst) ≤ _)) hi
      exact hc.trans (hs.trans le_self_add)
    · apply (hsup _ _ _ ?_).trans (Nat.add_le_add_right (Nat.le_max_right ..) w)
      intro i hi
      apply iht _
      apply hW.mono
      exact (Finset.le_sup (f := fun j => stmtCost t (idx ++ [j])) hi).trans le_add_self
  | bindIdx q args bound s ih =>
    apply hsup
    intro i hi
    apply ih _
    apply hW.mono
    exact (Finset.le_sup (f := fun j => stmtCost s (idx ++ [j])) hi).trans le_add_self
  | allocAs fmt len s ih =>
    simpa only [stmtPeak, Nat.add_assoc] using
      Nat.add_le_add_left (ih idx hW) (fmt.bytes * (len.eval idx).getD 0)
  | loop n s ih =>
    apply hsup
    intro i hi
    apply ih _
    apply hW.mono
    exact Finset.single_le_sum (f := fun j => stmtCost s (idx ++ [j]))
      (fun _ _ => (zero_le : (0 : Count Op Tst) ≤ _)) hi
  | frame ds args s ih =>
    simp only [stmtPeak]
    cases he : IExp.evalList idx ds <;>
      cases ho : IExp.evalList idx (args.map Operand.off) <;>
      first | exact Nat.zero_le _ | exact ih _ (by simpa [stmtCost, he, ho] using hW)

/-- A uniform primitive-workspace ceiling contributes only once above the stored allocation
peak. The premise bounds the workspace function on all operations and dimension lists;
establishing a smaller dimension-specific ceiling requires a separate shape invariant. -/
theorem stmtPeak_le_zero_add (W : Op → List ℕ → ℕ) (w : ℕ)
    (hW : ∀ o ds, W o ds ≤ w) (s : Stmt Op Tst) (idx : List ℕ) :
    stmtPeak W s idx ≤ stmtPeak (fun _ _ => 0) s idx + w := by
  have hsup (t : Finset ℕ) (f g : ℕ → ℕ) (h : ∀ i, f i ≤ g i + w) :
      t.sup f ≤ t.sup g + w := by
    apply Finset.sup_le
    intro i hi
    exact (h i).trans (Nat.add_le_add_right (Finset.le_sup hi) w)
  induction s generalizing idx with
  | skip | abort => exact Nat.zero_le _
  | call o ds ins outs =>
    simp only [stmtPeak]
    cases he : IExp.evalList idx ds with
    | none => exact Nat.zero_le _
    | some d => simpa only [Option.map_some, Option.getD_some, Nat.zero_add] using hW o d
  | seq s t ihs iht | ite q ds args s t ihs iht =>
    apply max_le
    · exact (ihs idx).trans (Nat.add_le_add_right (Nat.le_max_left ..) w)
    · exact (iht idx).trans (Nat.add_le_add_right (Nat.le_max_right ..) w)
  | whileFuel fuel q ds args s t ihs iht =>
    apply max_le
    · exact (hsup _ _ _ (fun i => ihs (idx ++ [i]))).trans
        (Nat.add_le_add_right (Nat.le_max_left ..) w)
    · exact (hsup _ _ _ (fun i => iht (idx ++ [i]))).trans
        (Nat.add_le_add_right (Nat.le_max_right ..) w)
  | bindIdx q args bound s ih => exact hsup _ _ _ (fun i => ih (idx ++ [i]))
  | allocAs fmt len s ih =>
    simpa only [stmtPeak, Nat.add_assoc] using
      Nat.add_le_add_left (ih idx) (fmt.bytes * (len.eval idx).getD 0)
  | loop n s ih => exact hsup _ _ _ (fun i => ih (idx ++ [i]))
  | frame ds args s ih =>
    simp only [stmtPeak]
    cases IExp.evalList idx ds <;> cases IExp.evalList idx (args.map Operand.off) <;>
      first | exact Nat.zero_le _ | exact ih _

end NLAlib.Ops
