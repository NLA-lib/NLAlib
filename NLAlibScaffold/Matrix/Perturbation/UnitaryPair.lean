/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Perturbation.UnitarySimilarity
public import NLAlib.Ops.Logic.Backward

/-!
# Perturbed unitary action on a pair

A sweep of rotations acts on two matrices with the same unitary factor: on the left of the
matrix being reduced to triangular form, $\mathbf{W}' = \mathbf{U}^{\mathsf{H}}(\mathbf{W} +
\mathbf{E})$, and by similarity on the matrix being iterated, $\mathbf{Z}' = \mathbf{U}^{\mathsf{H}}
(\mathbf{Z} + \mathbf{F})\mathbf{U}$. Both backward statements of a rounded implicit QR step
(the factorization $\mathbf{H} - s \approx \mathbf{Q}\mathbf{R}$ and the similarity $\mathbf{H}'
\approx \mathbf{Q}^{\mathsf{H}}\mathbf{H}\mathbf{Q}$, [BanksGarzaVargasSrivastava2022,
Definition 3.4]) are projections of this one relation, and the relation composes over the rounds
of the sweep because the unitary factor is shared.

The backward error $\varepsilon$ is dimensionless: the two perturbations are bounded by
$\varepsilon a$ and $\varepsilon b$ for fixed scales $a, b \ge 0$ (the norms of the inputs of the
sweep), so one real budget serves both components and `NLAlib.Ops.BackwardStep.loop_rel` applies
with the size $\max(\|\mathbf{W}\|_2 / a, \|\mathbf{Z}\|_2 / b)$.

## Main definitions

* `NLAlib.IsPerturbedUnitaryPair`: the relation.

## Main results

* `NLAlib.IsPerturbedUnitaryPair.refl`, `NLAlib.IsPerturbedUnitaryPair.trans`,
  `NLAlib.IsPerturbedUnitaryPair.mono`, `NLAlib.isBackwardErrorRel_isPerturbedUnitaryPair`.
* `NLAlib.IsPerturbedUnitaryPair.isPerturbedUnitarySimilar_snd`: the similarity component.
* `NLAlib.IsPerturbedUnitaryPair.exists_specNorm_sub_mul_le`: the factorization component.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- A perturbed unitary action on a pair at the scales $(a, b)$ with backward error
$\varepsilon$: $\mathbf{W}' = \mathbf{U}^{\mathsf{H}}(\mathbf{W} + \mathbf{E})$ and
$\mathbf{Z}' = \mathbf{U}^{\mathsf{H}}(\mathbf{Z} + \mathbf{F})\mathbf{U}$ for one square
$\mathbf{U}$ with orthonormal columns, $\|\mathbf{E}\|_2 \le \varepsilon a$ and
$\|\mathbf{F}\|_2 \le \varepsilon b$. -/
def IsPerturbedUnitaryPair (a b : ℝ) (ε : ℝ) (P P' : Matrix n n 𝕜 × Matrix n n 𝕜) : Prop :=
  ∃ U E F : Matrix n n 𝕜, HasOrthonormalCols U ∧ specNorm E ≤ ε * a ∧ specNorm F ≤ ε * b ∧
    P'.1 = Uᴴ * (P.1 + E) ∧ P'.2 = Uᴴ * (P.2 + F) * U

namespace IsPerturbedUnitaryPair

variable {a b : ℝ}

/-- Every pair is reached from itself with backward error $0$. -/
theorem refl (P : Matrix n n 𝕜 × Matrix n n 𝕜) : IsPerturbedUnitaryPair a b 0 P P :=
  ⟨1, 0, 0, hasOrthonormalCols_one, by simp, by simp, by simp, by simp⟩

/-- Backward errors add along a chain: the second perturbation is carried back through the
first unitary factor, which keeps its spectral norm. -/
theorem trans {ε₁ ε₂ : ℝ} {P P' P'' : Matrix n n 𝕜 × Matrix n n 𝕜}
    (h₁ : IsPerturbedUnitaryPair a b ε₁ P P') (h₂ : IsPerturbedUnitaryPair a b ε₂ P' P'') :
    IsPerturbedUnitaryPair a b (ε₁ + ε₂) P P'' := by
  sorry

/-- A larger bound is weaker, for nonnegative scales. -/
theorem mono (ha : 0 ≤ a) (hb : 0 ≤ b) {ε ε' : ℝ} {P P' : Matrix n n 𝕜 × Matrix n n 𝕜}
    (hε : ε ≤ ε') (h : IsPerturbedUnitaryPair a b ε P P') : IsPerturbedUnitaryPair a b ε' P P' := by
  sorry

/-- The similarity component is a perturbed unitary similarity with backward error
$\varepsilon b$. -/
theorem isPerturbedUnitarySimilar_snd {ε : ℝ} {P P' : Matrix n n 𝕜 × Matrix n n 𝕜}
    (h : IsPerturbedUnitaryPair a b ε P P') : IsPerturbedUnitarySimilar P.2 P'.2 (ε * b) := by
  sorry

/-- The factorization component: the same unitary factor reproduces the first input from the
first output up to $\varepsilon a$, $\|\mathbf{W} - \mathbf{U}\mathbf{W}'\|_2 \le \varepsilon a$,
together with the similarity of the second component. -/
theorem exists_specNorm_sub_mul_le {ε : ℝ} {P P' : Matrix n n 𝕜 × Matrix n n 𝕜}
    (h : IsPerturbedUnitaryPair a b ε P P') :
    ∃ U : Matrix n n 𝕜, HasOrthonormalCols U ∧ specNorm (P.1 - U * P'.1) ≤ ε * a ∧
      specNorm (P'.2 - Uᴴ * P.2 * U) ≤ ε * b := by
  sorry

end IsPerturbedUnitaryPair

/-- A perturbed unitary action on a pair at nonnegative scales is a backward-error relation of
the operation core. -/
theorem isBackwardErrorRel_isPerturbedUnitaryPair {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Ops.IsBackwardErrorRel (IsPerturbedUnitaryPair (𝕜 := 𝕜) (n := n) a b) := by
  sorry

end NLAlib
