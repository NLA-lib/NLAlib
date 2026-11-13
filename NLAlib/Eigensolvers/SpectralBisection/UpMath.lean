/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.SpectralBisection.ChildMath
public import NLAlib.Eigensolvers.SpectralBisection.Result

/-!
# Mathematical results reconstructed by reverse depth

Each reached node stores an ordinary matrix/eigenvalue pair computed by the existing pure
recursion with its remaining budget and indexed subtree samples. One reconstruction step is
exactly the constructor assembly of those child results.

## Main results

* `NLAlib.SpectralBisection.eighNodeResult`: the existing recursive result at one node.
* `NLAlib.SpectralBisection.StoresLevelResults`: ordinary represented results at a depth.
* `NLAlib.SpectralBisection.eighNodeResult_succ`: reconstruction is mathematical assembly.
-/

@[expose] public section

namespace NLAlib.SpectralBisection

/-- The existing recursive matrix algorithm on the indexed sample subtree of a node. -/
def eighNodeResult {K : Type} (F : FloatMachine K ℕ ℕ) (n fuel : ℕ) (R0 beta : K)
    (budget d lo : ℕ) (x : EighNode K) :=
  eighAux F n fuel R0 beta budget x.A x.R x.ε x.ℓ
    (eighSlotTree F n fuel R0 beta d lo x)

/-- The existing recursive results of the constructor-selected child nodes. -/
def eighNodeChildren {K : Type} (F : FloatMachine K ℕ ℕ) (n fuel : ℕ) (R0 beta : K)
    (budget d lo : ℕ) (x : EighNode K) (side : Bool) :=
  let step := eighStep F n fuel R0 beta x.A x.R x.ε x.ℓ (eighTapeSample n d lo)
  let p := eighNextParams F x.R x.ε x.ℓ
  eighNodeResult F n fuel R0 beta budget (d + 1) (step.childSlot lo side)
    ⟨step.childSize side, step.childMatrix side, p.1, p.2, x.ℓ + 1⟩

/-- Every reached node at this depth stores its ordinary recursive mathematical result.
The remaining budget is explicit, independently of the total traversal depth. -/
def StoresLevelResults {K : Type} (F : FloatMachine K ℕ ℕ) (n fuel : ℕ) (R0 beta : K)
    (root : EighNode K) (budget d : ℕ) (ua ea : ℕ × ℕ) (s : Ops.Store K) : Prop :=
  ∀ (a : List Bool) lo (x : EighNode K), a.length = d →
    eighLoc F n fuel R0 beta 0 0 root a = some (lo, x) →
      StoresResult n d lo ua ea (eighNodeResult F n fuel R0 beta budget d lo x) s

/-- One unit of the pure recursion assembles exactly the next-depth child results. -/
theorem eighNodeResult_succ {K : Type} (F : FloatMachine K ℕ ℕ) (n fuel : ℕ) (R0 beta : K)
    (budget d lo : ℕ) (x : EighNode K) :
    let step := eighStep F n fuel R0 beta x.A x.R x.ε x.ℓ (eighTapeSample n d lo)
    let p := eighNextParams F x.R x.ε x.ℓ
    eighNodeResult F n fuel R0 beta (budget + 1) d lo x =
      step.assemble F (fun side => eighNodeResult F n fuel R0 beta budget (d + 1)
        (step.childSlot lo side)
        ⟨step.childSize side, step.childMatrix side, p.1, p.2, x.ℓ + 1⟩) := by
  cases hs : eighStep F n fuel R0 beta x.A x.R x.ε x.ℓ (eighTapeSample n d lo) with
  | leaf U values => simp [eighNodeResult, eighAux, eighSlotTree, hs, EighStep.assemble]
  | shift side A sigma =>
    simp [eighNodeResult, eighAux, eighSlotTree, hs, EighStep.assemble,
      EighStep.childSize, EighStep.childMatrix, EighStep.childSlot]
  | split r hr Qp Qm Ap Am sigma =>
    simp [eighNodeResult, eighAux, eighSlotTree, hs, EighStep.assemble,
      EighStep.childSize, EighStep.childMatrix, EighStep.childSlot]

/-- Reached parent paths identify the represented child results needed by assembly. -/
theorem StoresLevelResults.children {K : Type} {F : FloatMachine K ℕ ℕ}
    {n fuel budget d lo : ℕ} {R0 beta : K} {root x : EighNode K} {a : List Bool}
    {ua ea : ℕ × ℕ} {s : Ops.Store K}
    (h : StoresLevelResults F n fuel R0 beta root budget (d + 1) ua ea s)
    (ha : a.length = d) (hx : eighLoc F n fuel R0 beta 0 0 root a = some (lo, x))
    (side : Bool)
    (hb : (eighStep F n fuel R0 beta x.A x.R x.ε x.ℓ
      (eighTapeSample n d lo)).HasChild side) :
    let step := eighStep F n fuel R0 beta x.A x.R x.ε x.ℓ (eighTapeSample n d lo)
    let p := eighNextParams F x.R x.ε x.ℓ
    StoresResult n (d + 1) (step.childSlot lo side) ua ea
      (eighNodeResult F n fuel R0 beta budget (d + 1) (step.childSlot lo side)
        ⟨step.childSize side, step.childMatrix side, p.1, p.2, x.ℓ + 1⟩) s := by
  exact h (a ++ [side]) _ _ (by simp [ha]) (eighLoc_child_of_hasChild F ha hx side hb)

/-- The depth-zero mathematical family contains the root's ordinary recursive output. -/
theorem StoresLevelResults.root {K : Type} {F : FloatMachine K ℕ ℕ}
    {n fuel budget : ℕ} {R0 beta : K} {root : EighNode K} {ua ea : ℕ × ℕ} {s : Ops.Store K}
    (h : StoresLevelResults F n fuel R0 beta root budget 0 ua ea s) :
    StoresResult n 0 0 ua ea (eighNodeResult F n fuel R0 beta budget 0 0 root) s :=
  h [] 0 root rfl rfl

end NLAlib.SpectralBisection
