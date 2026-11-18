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
* `NLAlib.IsPerturbedUnitaryPair.exists_witness`: the witnesses, with the inputs recovered from the
  outputs.
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
  obtain ⟨U₁, E₁, F₁, hU₁, hE₁, hF₁, h1, h2⟩ := h₁
  obtain ⟨U₂, E₂, F₂, hU₂, hE₂, hF₂, h3, h4⟩ := h₂
  have hI : U₁ᴴ * U₁ = 1 := hU₁.conjTranspose_mul_self
  have hJ : U₁ * U₁ᴴ = 1 := hU₁.mul_conjTranspose_self
  refine ⟨U₁ * U₂, E₁ + U₁ * E₂, F₁ + U₁ * F₂ * U₁ᴴ, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hasOrthonormalCols_iff, Matrix.conjTranspose_mul, Matrix.mul_assoc,
      ← Matrix.mul_assoc U₁ᴴ, hU₁.conjTranspose_mul_self, Matrix.one_mul,
      hU₂.conjTranspose_mul_self]
  · refine (specNorm_add_le _ _).trans ?_
    rw [add_mul]
    exact add_le_add hE₁ (by rwa [hU₁.specNorm_mul_left])
  · refine (specNorm_add_le _ _).trans ?_
    rw [add_mul]
    exact add_le_add hF₁ (by rwa [hU₁.specNorm_mul_conjTranspose_right, hU₁.specNorm_mul_left])
  · rw [h3, h1]
    simp only [Matrix.conjTranspose_mul, Matrix.mul_add, Matrix.mul_assoc]
    simp only [← Matrix.mul_assoc U₁ᴴ U₁, hI, Matrix.one_mul]
    abel
  · rw [h4, h2]
    simp only [Matrix.conjTranspose_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
    simp only [← Matrix.mul_assoc U₁ᴴ U₁, hI, Matrix.one_mul]
    abel

/-- A larger bound is weaker, for nonnegative scales. -/
theorem mono (ha : 0 ≤ a) (hb : 0 ≤ b) {ε ε' : ℝ} {P P' : Matrix n n 𝕜 × Matrix n n 𝕜}
    (hε : ε ≤ ε') (h : IsPerturbedUnitaryPair a b ε P P') : IsPerturbedUnitaryPair a b ε' P P' := by
  obtain ⟨U, E, F, hU, hE, hF, h1, h2⟩ := h
  exact ⟨U, E, F, hU, hE.trans (mul_le_mul_of_nonneg_right hε ha),
    hF.trans (mul_le_mul_of_nonneg_right hε hb), h1, h2⟩

/-- The similarity component is a perturbed unitary similarity with backward error
$\varepsilon b$. -/
theorem isPerturbedUnitarySimilar_snd {ε : ℝ} {P P' : Matrix n n 𝕜 × Matrix n n 𝕜}
    (h : IsPerturbedUnitaryPair a b ε P P') : IsPerturbedUnitarySimilar P.2 P'.2 (ε * b) := by
  obtain ⟨U, E, F, hU, _, hF, _, h2⟩ := h
  exact ⟨U, F, hU, hF, h2⟩

/-- The factorization component: the same unitary factor reproduces the first input from the
first output up to $\varepsilon a$, $\|\mathbf{W} - \mathbf{U}\mathbf{W}'\|_2 \le \varepsilon a$,
together with the similarity of the second component. -/
theorem exists_specNorm_sub_mul_le {ε : ℝ} {P P' : Matrix n n 𝕜 × Matrix n n 𝕜}
    (h : IsPerturbedUnitaryPair a b ε P P') :
    ∃ U : Matrix n n 𝕜, HasOrthonormalCols U ∧ specNorm (P.1 - U * P'.1) ≤ ε * a ∧
      specNorm (P'.2 - Uᴴ * P.2 * U) ≤ ε * b := by
  obtain ⟨U, E, F, hU, hE, hF, h1, h2⟩ := h
  have hJ : U * Uᴴ = 1 := hU.mul_conjTranspose_self
  refine ⟨U, hU, ?_, ?_⟩
  · have : P.1 - U * P'.1 = -E := by
      rw [h1, ← Matrix.mul_assoc, hJ, Matrix.one_mul]
      abel
    rwa [this, specNorm_neg]
  · have : P'.2 - Uᴴ * P.2 * U = Uᴴ * F * U := by
      rw [h2, Matrix.mul_add, Matrix.add_mul]
      abel
    rw [this, hU.specNorm_conjTranspose_mul_mul]
    exact hF

/-- The witnesses of a perturbed pair, solved for the inputs: the unitary factor
$\mathbf{U}$ ($\mathbf{U}\mathbf{U}^{\mathsf H} = \mathbf{I}$) and the perturbations
$\|\mathbf{E}\|_2 \le \varepsilon a$, $\|\mathbf{F}\|_2 \le \varepsilon b$ as data, with both
the forward identities $\mathbf{W}' = \mathbf{U}^{\mathsf H}(\mathbf{W} + \mathbf{E})$,
$\mathbf{Z}' = \mathbf{U}^{\mathsf H}(\mathbf{Z} + \mathbf{F})\mathbf{U}$ and the inputs
recovered from the outputs, $\mathbf{W} + \mathbf{E} = \mathbf{U}\mathbf{W}'$ and
$\mathbf{Z} + \mathbf{F} = \mathbf{U}\mathbf{Z}'\mathbf{U}^{\mathsf H}$: the form a consumer
needs to re-embed the outputs into a larger matrix. -/
theorem exists_witness {ε : ℝ} {P P' : Matrix n n 𝕜 × Matrix n n 𝕜}
    (h : IsPerturbedUnitaryPair a b ε P P') :
    ∃ U E F : Matrix n n 𝕜, HasOrthonormalCols U ∧ U * Uᴴ = 1 ∧ specNorm E ≤ ε * a ∧
      specNorm F ≤ ε * b ∧ P'.1 = Uᴴ * (P.1 + E) ∧ P'.2 = Uᴴ * (P.2 + F) * U ∧
      P.1 + E = U * P'.1 ∧ P.2 + F = U * P'.2 * Uᴴ := by
  obtain ⟨U, E, F, hU, hE, hF, h1, h2⟩ := h
  have hJ : U * Uᴴ = 1 := hU.mul_conjTranspose_self
  refine ⟨U, E, F, hU, hJ, hE, hF, h1, h2, ?_, ?_⟩
  · rw [h1, ← Matrix.mul_assoc, hJ, Matrix.one_mul]
  · rw [h2, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hJ, Matrix.one_mul, Matrix.mul_assoc, hJ,
      Matrix.mul_one]

end IsPerturbedUnitaryPair

/-- A perturbed unitary action on a pair at nonnegative scales is a backward-error relation of
the operation core. -/
theorem isBackwardErrorRel_isPerturbedUnitaryPair {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Ops.IsBackwardErrorRel (IsPerturbedUnitaryPair (𝕜 := 𝕜) (n := n) a b) :=
  ⟨IsPerturbedUnitaryPair.refl, IsPerturbedUnitaryPair.trans,
    IsPerturbedUnitaryPair.mono ha hb⟩

/-- **The bridge to the witnessed relation**: at the first scale $0$ the pair relation leaves no
error on the first component, so on $(\mathbf{X}^{\mathsf H}, \mathbf{A})$ with $\mathbf{X}$
unitary it is the witnessed similarity by $\mathbf{X}^{\mathsf H}\mathbf{X}'$. A chain of witnessed
steps composes through `NLAlib.Ops.BackwardStep` with
`NLAlib.isBackwardErrorRel_isPerturbedUnitaryPair` at the scales $(0, 1)$. -/
theorem isPerturbedUnitaryPair_zero_iff {X X' A B : Matrix n n 𝕜} {ε : ℝ} (hX : X * Xᴴ = 1) :
    IsPerturbedUnitaryPair 0 1 ε (Xᴴ, A) (X'ᴴ, B) ↔
      IsPerturbedUnitarySimilarBy (Xᴴ * X') A B ε := by
  have hX' : Xᴴ * X = 1 := mul_eq_one_comm.mp hX
  constructor
  · rintro ⟨U, E, F, hU, hE, hF, h1, h2⟩
    have hE0 : E = 0 :=
      specNorm_eq_zero_iff.mp (le_antisymm (by simpa using hE) (specNorm_nonneg E))
    have hXU : X' = X * U := by
      have h1' : X'ᴴ = Uᴴ * Xᴴ := by simpa [hE0] using h1
      rw [← Matrix.conjTranspose_conjTranspose X', h1', Matrix.conjTranspose_mul,
        Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_conjTranspose]
    have hV : Xᴴ * X' = U := by rw [hXU, ← Matrix.mul_assoc, hX', Matrix.one_mul]
    rw [hV]
    exact ⟨hU, F, by simpa using hF, h2⟩
  · rintro ⟨hV, E, hE, h⟩
    refine ⟨Xᴴ * X', 0, E, hV, by simp, by simpa using hE, ?_, h⟩
    simp only [add_zero, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.mul_assoc, hX, Matrix.mul_one]

end NLAlib
