/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Perturbation.UnitarySimilarity
public import NLAlib.Matrix.Spectral.EigenvalueListing
public import NLAlib.Matrix.Subspaces.Frames

/-!
# Backward-error relations are closed

The relations of backward error analysis are closed sets of pairs of matrices: "$\mathbf{B}$ is a
perturbed unitary similarity of $\mathbf{A}$ with error $\varepsilon$", and "$\mu$ lists the
eigenvalues of $\mathbf{A} + \mathbf{F}$ for some $\|\mathbf{F}\|_2 \le \beta$". Each is the
projection of a closed set along a compact factor (the matrices with orthonormal columns, a
closed ball of the spectral norm). Closed sets are Borel, so these relations can be checked on
the result of a randomized computation by a measurable event.

## Main results

* `NLAlib.isClosed_setOf_exists_mem_of_isCompact`: the projection of a closed set along a compact
  set is closed.
* `NLAlib.isClosed_setOf_isPerturbedUnitarySimilar`.
* `NLAlib.isClosed_setOf_exists_specNorm_le_isEigenvalueListing`.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

/-- **The projection of a closed set along a compact set is closed**: if $C \subseteq X \times Y$
is closed and $K \subseteq Y$ is compact, the points $x$ with $(x, y) \in C$ for some $y \in K$
form a closed set. -/
theorem isClosed_setOf_exists_mem_of_isCompact {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {K : Set Y} (hK : IsCompact K) {C : Set (X × Y)} (hC : IsClosed C) :
    IsClosed {x | ∃ y ∈ K, (x, y) ∈ C} := by
  have := isCompact_iff_compactSpace.mp hK
  have hC' : IsClosed {p : X × K | (p.1, (p.2 : Y)) ∈ C} :=
    hC.preimage (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
  convert isClosedMap_fst_of_compactSpace _ hC' using 1
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_image, Prod.exists, Subtype.exists, exists_and_right,
    exists_eq_right]
  exact ⟨fun ⟨y, hy, h⟩ => ⟨y, hy, h⟩, fun ⟨y, hy, h⟩ => ⟨y, hy, h⟩⟩

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- **Perturbed unitary similarity is a closed relation**: for every $\varepsilon$ the pairs
$(\mathbf{A}, \mathbf{B})$ of square matrices with
$\mathbf{B} = \mathbf{U}^{\mathsf{H}}(\mathbf{A} + \mathbf{E})\mathbf{U}$ for some $\mathbf{U}$
with orthonormal columns and some $\|\mathbf{E}\|_2 \le \varepsilon$ form a closed set. -/
theorem isClosed_setOf_isPerturbedUnitarySimilar (ε : ℝ) :
    IsClosed {p : Matrix n n 𝕜 × Matrix n n 𝕜 | IsPerturbedUnitarySimilar p.1 p.2 ε} := by
  have hC : IsClosed {q : (Matrix n n 𝕜 × Matrix n n 𝕜) × Matrix n n 𝕜 |
      specNorm (q.2 * q.1.2 * q.2ᴴ - q.1.1) ≤ ε} :=
    isClosed_le (continuous_specNorm.comp (((continuous_snd.matrix_mul
      (continuous_snd.comp continuous_fst)).matrix_mul continuous_snd.matrix_conjTranspose).sub
      (continuous_fst.comp continuous_fst))) continuous_const
  convert isClosed_setOf_exists_mem_of_isCompact isCompact_setOf_hasOrthonormalCols hC using 1
  ext ⟨A, B⟩
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨U, E, hU, hE, rfl⟩
    have hU' : U * Uᴴ = 1 := hU.mul_conjTranspose_self
    refine ⟨U, hU, ?_⟩
    have : U * (Uᴴ * (A + E) * U) * Uᴴ = A + E := by
      simp only [← Matrix.mul_assoc, hU', Matrix.one_mul]
      rw [Matrix.mul_assoc, hU', Matrix.mul_one]
    simpa [this] using hE
  · rintro ⟨U, hU, hE⟩
    have hU' : Uᴴ * U = 1 := hU
    refine ⟨U, U * B * Uᴴ - A, hU, hE, ?_⟩
    rw [add_sub_cancel]
    simp only [← Matrix.mul_assoc, hU', Matrix.one_mul]
    rw [Matrix.mul_assoc, hU', Matrix.mul_one]

variable {ι : Type*} [Fintype ι]

/-- **A backward-accurate eigenvalue listing is a closed relation**: for every $\beta$ the pairs
$(\mathbf{A}, \mu)$ of a complex square matrix and a family such that $\mu$ lists the eigenvalues
of $\mathbf{A} + \mathbf{F}$, with multiplicity, for some $\|\mathbf{F}\|_2 \le \beta$, form a
closed set. -/
theorem isClosed_setOf_exists_specNorm_le_isEigenvalueListing (β : ℝ) :
    IsClosed {p : Matrix n n ℂ × (ι → ℂ) |
      ∃ F : Matrix n n ℂ, specNorm F ≤ β ∧ IsEigenvalueListing (p.1 + F) p.2} := by
  have hK : IsCompact {F : Matrix n n ℂ | specNorm F ≤ β} := by
    have hbox := isCompact_univ_pi fun _ : n => isCompact_univ_pi fun _ : n =>
      isCompact_closedBall (0 : ℂ) β
    refine hbox.of_isClosed_subset (isClosed_le continuous_specNorm continuous_const)
      fun (F : Matrix n n ℂ) hF i _ j _ => mem_closedBall_zero_iff.mpr ?_
    exact (norm_apply_le_specNorm F i j).trans hF
  have hC : IsClosed {q : (Matrix n n ℂ × (ι → ℂ)) × Matrix n n ℂ |
      ∀ t : ℂ, (Matrix.scalar n t - (q.1.1 + q.2)).det = ∏ i, (t - q.1.2 i)} := by
    rw [Set.ofPred_forall]
    refine isClosed_iInter fun t : ℂ => isClosed_eq ?_ ?_
    · exact (continuous_const.sub ((continuous_fst.comp continuous_fst).add
        continuous_snd)).matrix_det
    · exact continuous_finsetProd _ fun i _ => continuous_const.sub
        ((continuous_apply i).comp (continuous_snd.comp continuous_fst))
  convert isClosed_setOf_exists_mem_of_isCompact hK hC using 1
  ext ⟨A, μ⟩
  simp only [Set.mem_ofPred_eq]
  refine exists_congr fun F => and_congr Iff.rfl ?_
  rw [isEigenvalueListing_iff]
  constructor
  · intro h t
    have := congrArg (Polynomial.eval t) h
    rw [Matrix.eval_charpoly, Polynomial.eval_prod] at this
    simpa using this
  · intro h
    refine Polynomial.funext fun t => ?_
    rw [Matrix.eval_charpoly, Polynomial.eval_prod, h t]
    simp

end NLAlib
