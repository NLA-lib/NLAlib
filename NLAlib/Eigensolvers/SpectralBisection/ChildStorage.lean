/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.SpectralBisection.State
public import NLAlib.Eigensolvers.SpectralBisection.Assembly
public import NLAlib.Matrix.FinitePrecision.SpectralBisection.Levels

/-!
# Child inputs represented by a stored mathematical outcome

A stored node outcome already contains each occupied child's size literal and packed matrix.
The pure constructor projections identify its dimension, matrix and slot. These readers are
independent of the program's branch syntax and of numerical accuracy assumptions.

## Main results

* `NLAlib.SpectralBisection.StoresStep.child_inputs`: actual inputs of any occupied child.
-/

@[expose] public section

namespace NLAlib.SpectralBisection

open Ops

/-- Matrix, result and parent metadata outputs of a mathematical outcome. Child size
words are excluded so their exact effects can be tracked separately. -/
def stepPayloadFp {K : Type} (n d lo : ℕ) (ma ua qa ea sz kd kp : ℕ × ℕ) {k : ℕ} :
    EighStep K k → Fp
  | step@(.leaf ..) => Fp.blocks (stepOutputs n d lo ma ua qa ea sz kd kp step)
      (stepOutputLengths step)
  | .shift .. => Fp.blocks
      [(ma.1, ma.2 + 2 * (n * n) * (d + 1) + 2 * n * lo),
        (kd.1, kd.2 + n * d + lo)] [2 * (k * k), 1]
  | .split r .. => Fp.blocks
      [(qa.1, qa.2 + 2 * (n * n) * d + 2 * n * lo),
        (qa.1, qa.2 + 2 * (n * n) * d + 2 * n * lo + 2 * (k * r)),
        (ma.1, ma.2 + 2 * (n * n) * (d + 1) + 2 * n * lo),
        (ma.1, ma.2 + 2 * (n * n) * (d + 1) + 2 * n * (lo + r)),
        (kd.1, kd.2 + n * d + lo), (kp.1, kp.2 + n * d + lo)]
      [2 * (k * r), 2 * (k * (k - r)), 2 * (r * r), 2 * ((k - r) * (k - r)), 1, 1]

/-- Every written cell is a payload cell or one of the occupied child size cells. -/
theorem stepFp_payload_or_child {K : Type} {n d lo k b i : ℕ}
    (ma ua qa ea sz kd kp : ℕ × ℕ) (step : EighStep K k)
    (h : Fp.blocks (stepOutputs n d lo ma ua qa ea sz kd kp step)
      (stepOutputLengths step) b i) :
    stepPayloadFp n d lo ma ua qa ea sz kd kp step b i ∨
      ∃ side, step.HasChild side ∧ b = sz.1 ∧
        i = sz.2 + n * (d + 1) + step.childSlot lo side := by
  cases step with
  | leaf U values => exact Or.inl h
  | shift side A sigma =>
    simp only [stepOutputs, stepOutputLengths, Fp.blocks, Pi.sup_apply,
      sup_Prop_eq, Pi.bot_apply] at h
    rcases h with h | h | h | h
    · exact Or.inl (Or.inl h)
    · exact Or.inr ⟨side, rfl, h.1, by
        simp only [EighStep.childSlot]; have := h.2; omega⟩
    · exact Or.inl (Or.inr (Or.inl h))
    · exact False.elim h
  | split r hr Qp Qm Ap Am sigma =>
    simp only [stepOutputs, stepOutputLengths, splitOutputs, splitOutputLengths,
      Fp.blocks, Pi.sup_apply, sup_Prop_eq, Pi.bot_apply] at h
    rcases h with h | h | h | h | h | h | h | h | h
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr (Or.inl h))
    · exact Or.inl (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl h))))
    · exact Or.inr ⟨true, trivial, h.1, by
        simp only [EighStep.childSlot]; have := h.2; omega⟩
    · exact Or.inr ⟨false, trivial, h.1, by
        simp only [EighStep.childSlot]; have := h.2; omega⟩
    · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
    · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
    · exact False.elim h

/-- An unwritten child slot stays outside the exact step footprint. Spatial separation
from payload outputs permits the size arena to share a buffer with other arenas. -/
theorem not_stepFp_size_of_no_child {K : Type} {n d lo k j : ℕ}
    (ma ua qa ea sz kd kp : ℕ × ℕ) (step : EighStep K k) (hj : j < n)
    (hPayload : Fp.Disj (Store.inBlock sz.1 (sz.2 + n * (d + 1)) n)
      (stepPayloadFp n d lo ma ua qa ea sz kd kp step))
    (hAbsent : ∀ side, step.HasChild side → j ≠ step.childSlot lo side) :
    ¬ Fp.blocks (stepOutputs n d lo ma ua qa ea sz kd kp step)
      (stepOutputLengths step) sz.1 (sz.2 + n * (d + 1) + j) := by
  intro h
  rcases stepFp_payload_or_child ma ua qa ea sz kd kp step h with h | ⟨side, hs, _, hi⟩
  · exact hPayload _ _ ⟨rfl, by omega, by omega⟩ h
  · exact hAbsent side hs (by omega)

/-- Extending a reached path by an occupied side reaches precisely the constructor's child
slot and matrix. This is a property of the mathematical traversal, independent of storage. -/
theorem eighLoc_child_of_hasChild {K : Type} (F : FloatMachine K ℕ ℕ)
    {n fuel d lo : ℕ} {R0 beta : K} {root x : EighNode K} {a : List Bool}
    (ha : a.length = d) (hx : eighLoc F n fuel R0 beta 0 0 root a = some (lo, x))
    (side : Bool)
    (hb : (eighStep F n fuel R0 beta x.A x.R x.ε x.ℓ
      (eighTapeSample n d lo)).HasChild side) :
    let step := eighStep F n fuel R0 beta x.A x.R x.ε x.ℓ (eighTapeSample n d lo)
    let p := eighNextParams F x.R x.ε x.ℓ
    eighLoc F n fuel R0 beta 0 0 root (a ++ [side]) =
      some (step.childSlot lo side,
        ⟨step.childSize side, step.childMatrix side, p.1, p.2, x.ℓ + 1⟩) := by
  rw [eighLoc_append_singleton, hx]
  simp only [Option.bind_some, ha, Nat.zero_add]
  cases hs : eighStep F n fuel R0 beta x.A x.R x.ε x.ℓ (eighTapeSample n d lo) with
  | leaf U values => simp only [hs, EighStep.HasChild] at hb
  | shift b A sigma =>
    simp only [hs, EighStep.HasChild] at hb
    subst side
    simp [eighLoc, hs, EighStep.childSlot, EighStep.childSize, EighStep.childMatrix]
  | split r hr Qp Qm Ap Am sigma =>
    cases side <;>
      simp [eighLoc, hs, EighStep.childSlot, EighStep.childSize, EighStep.childMatrix]

/-- A slot absent from the next mathematical level cannot be a size output of any reached
parent. The remaining payload disjointness is purely spatial arena geometry. -/
theorem not_stepFp_size_of_absent_next {K : Type} (F : FloatMachine K ℕ ℕ)
    {n fuel d lo j : ℕ} {R0 beta : K} {root x : EighNode K} {a : List Bool}
    (ma ua qa ea sz kd kp : ℕ × ℕ) (hj : j < n) (ha : a.length = d)
    (hx : eighLoc F n fuel R0 beta 0 0 root a = some (lo, x))
    (hPayload : Fp.Disj (Store.inBlock sz.1 (sz.2 + n * (d + 1)) n)
      (stepPayloadFp n d lo ma ua qa ea sz kd kp
        (eighStep F n fuel R0 beta x.A x.R x.ε x.ℓ (eighTapeSample n d lo))))
    (hAbsent : ∀ (path : List Bool) (y : EighNode K), path.length = d + 1 →
      eighLoc F n fuel R0 beta 0 0 root path ≠ some (j, y)) :
    ¬ Fp.blocks (stepOutputs n d lo ma ua qa ea sz kd kp
      (eighStep F n fuel R0 beta x.A x.R x.ε x.ℓ (eighTapeSample n d lo)))
      (stepOutputLengths
        (eighStep F n fuel R0 beta x.A x.R x.ε x.ℓ (eighTapeSample n d lo)))
      sz.1 (sz.2 + n * (d + 1) + j) := by
  apply not_stepFp_size_of_no_child ma ua qa ea sz kd kp _ hj hPayload
  intro side hb hslot
  have hc := eighLoc_child_of_hasChild F ha hx side hb
  dsimp only at hc
  rw [← hslot] at hc
  exact hAbsent (a ++ [side]) _ (by simp [ha]) hc

/-- Every occupied mathematical child has its actual size word and packed input matrix
stored at the next level and its constructor-selected slot. -/
theorem StoresStep.child_inputs {K : Type} {M : Machine K} {R : K} {n d lo k : ℕ}
    {ma ua qa ea sz kd kp : ℕ × ℕ} {step : EighStep K k} {m : Mem K}
    (h : StoresStep M R n d lo ma ua qa ea sz kd kp step m) (b : Bool)
    (hb : step.HasChild b) :
    m.store.get sz.1 (sz.2 + n * (d + 1) + step.childSlot lo b) =
        some (M.lit (step.childSize b : ℚ)) ∧
      m.store.readBlock ma.1 (ma.2 + 2 * (n * n) * (d + 1) + 2 * n * step.childSlot lo b)
        (2 * (step.childSize b * step.childSize b)) =
          some ((EntryCodec.pair K).packFinMatrix (step.childMatrix b)) := by
  cases step with
  | leaf U values => exact False.elim hb
  | shift side A sigma =>
    change b = side at hb
    subst b
    constructor
    · simpa [stepOutputs, stepOutputLengths, stepOutputWords, EighStep.childSize,
        EighStep.childSlot] using Mem.get_of_readBlocks_getD h.2 (i := 1)
          (by simp [stepOutputs, stepOutputLengths]) rfl rfl
    · simpa [stepOutputs, stepOutputLengths, stepOutputWords, EighStep.childSize,
        EighStep.childSlot, EighStep.childMatrix] using Mem.readBlocks_getD h.2 (i := 0)
          (by simp [stepOutputs, stepOutputLengths])
  | split r hr Qp Qm Ap Am sigma =>
    cases b with
    | false =>
      constructor
      · simpa [stepOutputs, stepOutputLengths, stepOutputWords, splitOutputs, splitOutputLengths,
          EighStep.childSize, EighStep.childSlot, Nat.add_assoc] using
          Mem.get_of_readBlocks_getD h.2 (i := 5)
            (by simp [stepOutputs, stepOutputLengths, splitOutputs, splitOutputLengths]) rfl rfl
      · simpa [stepOutputs, stepOutputLengths, stepOutputWords, splitOutputs, splitOutputLengths,
          EighStep.childSize, EighStep.childSlot, EighStep.childMatrix] using
          Mem.readBlocks_getD h.2 (i := 3)
            (by simp [stepOutputs, stepOutputLengths, splitOutputs, splitOutputLengths])
    | true =>
      constructor
      · simpa [stepOutputs, stepOutputLengths, stepOutputWords, splitOutputs, splitOutputLengths,
          EighStep.childSize, EighStep.childSlot] using Mem.get_of_readBlocks_getD h.2 (i := 4)
            (by simp [stepOutputs, stepOutputLengths, splitOutputs, splitOutputLengths]) rfl rfl
      · simpa [stepOutputs, stepOutputLengths, stepOutputWords, splitOutputs, splitOutputLengths,
          EighStep.childSize, EighStep.childSlot, EighStep.childMatrix] using
          Mem.readBlocks_getD h.2 (i := 2)
            (by simp [stepOutputs, stepOutputLengths, splitOutputs, splitOutputLengths])

end NLAlib.SpectralBisection
