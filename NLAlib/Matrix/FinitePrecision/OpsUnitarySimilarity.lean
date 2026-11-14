/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Perturbation.UnitarySimilarity
public import NLAlib.Ops.Logic.Backward

/-!
# Backward steps of unitary similarity

A perturbed unitary similarity (`NLAlib.IsPerturbedUnitarySimilar`) is a backward-error relation
of the operation core (`NLAlib.Ops.IsBackwardErrorRel`), so a program whose steps return a
perturbed unitary similarity of the stored matrix is analysed by the composition rules of
`NLAlib.Ops.BackwardStep`: the backward errors of a sequence add, those of a loop are summed.

A block specification in exact arithmetic that returns $\mathbf{U}^{\mathsf{H}}\mathbf{A}
\mathbf{U}$ for a unitary $\mathbf{U}$, the form of the exact shifted QR iteration and decoupling,
is a backward step with error $0$ (`NLAlib.Ops.BackwardStep.of_unitarySimilar`).

## Main results

* `NLAlib.isBackwardErrorRel_isPerturbedUnitarySimilar`: the relation.
* `NLAlib.Ops.BackwardStep.of_unitarySimilar`: an exact unitary similarity is a backward step
  with error $0$.
* `NLAlib.Ops.BackwardStep.of_specNorm_sub_le`: an exact unitary similarity up to an error
  $\varepsilon$ is a backward step with error $\varepsilon$.

`NLAlib.Ops.BackwardStep.loop_rel` applies with the spectral norm as the size of the state, by
`NLAlib.IsPerturbedUnitarySimilar.specNorm_le`: a per-round error $\nu\|\mathbf{H}_k\|_2$
sums to $((1 + \nu)^N - 1)\|\mathbf{H}\|_2$.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- A perturbed unitary similarity is a backward-error relation: backward error $0$ is
reflexive, backward errors add, and a larger bound is weaker. -/
theorem isBackwardErrorRel_isPerturbedUnitarySimilar :
    Ops.IsBackwardErrorRel fun ε (A B : Matrix n n 𝕜) => IsPerturbedUnitarySimilar A B ε :=
  ⟨IsPerturbedUnitarySimilar.refl, fun h₁ h₂ => h₁.trans h₂, fun hε h => h.mono hε⟩

namespace Ops

variable {Op Tst K : Type} {md : Mode} {I : Interp Op Tst K} {τ : Tape K} {c : Stmt Op Tst}
  {ρ : Env} {F : Fp} {S S' : Matrix n n 𝕜 → Mem K → Prop}

/-- An exact unitary similarity is a backward step with error $0$: if from every memory
holding $\mathbf{A}$ the run of `c` ends holding $\mathbf{U}^{\mathsf{H}}\mathbf{A}\mathbf{U}$ for
some $\mathbf{U}$ with orthonormal columns, it is a backward step for the perturbed unitary
similarity with error $0$. -/
theorem BackwardStep.of_unitarySimilar
    (h : ∀ A m, S A m → Writes md I τ c ρ F (fun m' => ∃ U B : Matrix n n 𝕜,
      HasOrthonormalCols U ∧ B = Uᴴ * A * U ∧ S' B m') m) :
    BackwardStep md I τ c ρ F (fun ε A B => IsPerturbedUnitarySimilar A B ε) S S' 0 :=
  fun A m hA => (h A m hA).mono le_rfl fun _ _ ⟨_, B, hU, hB, hS⟩ =>
    ⟨B, hB ▸ hU.isPerturbedUnitarySimilar A, hS⟩

/-- A step that returns an exact unitary similarity up to an error is a backward step: if from
every memory holding $\mathbf{A}$ the run of `c` ends holding $\mathbf{B}$ with
$\|\mathbf{B} - \mathbf{U}^{\mathsf{H}}\mathbf{A}\mathbf{U}\|_2 \le \varepsilon$ for some
$\mathbf{U}$ with orthonormal columns, it is a backward step for the perturbed unitary
similarity with error $\varepsilon$. The form a rounded kernel contract gives. -/
theorem BackwardStep.of_specNorm_sub_le {ε : ℝ}
    (h : ∀ A m, S A m → Writes md I τ c ρ F (fun m' => ∃ U B : Matrix n n 𝕜,
      HasOrthonormalCols U ∧ specNorm (B - Uᴴ * A * U) ≤ ε ∧ S' B m') m) :
    BackwardStep md I τ c ρ F (fun ε A B => IsPerturbedUnitarySimilar A B ε) S S' ε :=
  fun A m hA => (h A m hA).mono le_rfl fun _ _ ⟨_, B, hU, hB, hS⟩ =>
    ⟨B, IsPerturbedUnitarySimilar.of_specNorm_sub_le hU hB, hS⟩

end Ops

end NLAlib
