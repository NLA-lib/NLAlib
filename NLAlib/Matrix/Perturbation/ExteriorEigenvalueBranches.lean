/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Perturbation.SimpleEigenvalueBranch
public import NLAlib.Matrix.Spectral.SimpleSpectrum

/-!
# Eigenvalue branches outside a disk

For a pencil with distinct diagonal leading coefficients, all eigenvalues admit a consistent
analytic labeling outside a sufficiently large disk. Hermitian coefficients give the
conjugation identity used to deform the trace contour.

## Main results

* `Matrix.IsHermitian.exists_exterior_branches_sub_diagonal_conj_eq`.
-/

@[expose] public section

section

open Filter

open scoped Matrix Topology

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

open scoped Matrix.Norms.L2Operator in
/-- Distinct diagonal slopes give a complete indexed collection of distinct analytic eigenvalue
branches outside one common disk. Their affine offsets converge to the corresponding diagonal
entries of the perturbation, as in Stahl (2013), Theorem 2. [Stahl2013, §§2–5]. -/
theorem exists_exterior_eigenvalue_branches_of_diagonal
    (d : n → ℂ) (hd : Function.Injective d) (A : Matrix n n ℂ) :
    ∃ R : ℝ, 0 < R ∧ ∃ branch : n → ℂ → ℂ,
      (∀ i, DifferentiableOn ℂ (branch i) {z | R < ‖z‖} ∧
        Tendsto (fun z => branch i z - z * d i) (Bornology.cobounded ℂ) (𝓝 (A i i))) ∧
      ∀ z, R < ‖z‖ →
        (∀ i, branch i z ∈ spectrum ℂ (A + z • Matrix.diagonal d)) ∧
        Function.Injective (fun i => branch i z) := by
  classical
  choose φ g hφ₀ hφa hga hφspec hφeq using
    fun i => exists_analytic_eigenvalue_branch_diagonal_expansion d hd A i
  let branch : n → ℂ → ℂ := fun i z => z * φ i z⁻¹
  have hi : Tendsto (fun z : ℂ => z⁻¹) (Bornology.cobounded ℂ) (𝓝 0) :=
    tendsto_inv₀_cobounded
  have hpair : ∀ᶠ t in 𝓝 (0 : ℂ), Function.Injective (fun i => φ i t) := by
    have hp : ∀ i j, ∀ᶠ t in 𝓝 (0 : ℂ), φ i t = φ j t → i = j := by
      intro i j
      by_cases hij : i = j
      · exact Eventually.of_forall (fun _ _ => hij)
      · have hn : φ i 0 - φ j 0 ≠ 0 := by
          rw [hφ₀, hφ₀]
          exact sub_ne_zero.mpr (hd.ne hij)
        filter_upwards [((hφa i).continuousAt.sub (hφa j).continuousAt).tendsto.eventually_ne hn]
          with t ht heq
        exact False.elim (ht (sub_eq_zero.mpr heq))
    have hp' : ∀ᶠ t in 𝓝 (0 : ℂ), ∀ i j, φ i t = φ j t → i = j := by
      simpa only [Filter.eventually_all] using hp
    exact hp'
  have hall : ∀ᶠ t in 𝓝 (0 : ℂ),
      ∀ i, AnalyticAt ℂ (φ i) t ∧ φ i t ∈ spectrum ℂ (Matrix.diagonal d + t • A) := by
    simp only [Filter.eventually_all]
    intro i
    exact (hφa i).eventually_analyticAt.and (hφspec i)
  have hnz : ∀ᶠ z : ℂ in Bornology.cobounded ℂ, z ≠ 0 := by
    filter_upwards [eventually_cobounded_le_norm (1 : ℝ)] with z hz
    intro hzero
    norm_num [hzero] at hz
  have hext : ∀ᶠ z : ℂ in Bornology.cobounded ℂ,
      (∀ i, AnalyticAt ℂ (branch i) z ∧
        branch i z ∈ spectrum ℂ (A + z • Matrix.diagonal d)) ∧
        Function.Injective (fun i => branch i z) := by
    filter_upwards [hi.eventually hall, hi.eventually hpair, hnz] with z hz hp hzne
    refine ⟨fun i => ⟨?_, ?_⟩, ?_⟩
    · exact analyticAt_id.mul ((hz i).1.comp (analyticAt_inv hzne))
    · have hs := (spectrum.smul_mem_smul_iff (R := ℂ)
        (r := Units.mk0 z hzne) (a := Matrix.diagonal d + z⁻¹ • A) (s := φ i z⁻¹)).mpr
          (hz i).2
      simpa only [Units.smul_def, Units.val_mk0, smul_eq_mul, smul_add,
        smul_smul, mul_inv_cancel₀ hzne, one_smul, add_comm] using hs
    · intro i j hij
      apply hp
      exact mul_left_cancel₀ hzne hij
  obtain ⟨R, _, hR⟩ := Filter.hasBasis_cobounded_norm.eventually_iff.mp hext
  refine ⟨max R 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), branch, ?_, ?_⟩
  · intro i
    refine ⟨fun z hz =>
      ((hR ((le_max_left R 1).trans hz.le)).1 i).1.differentiableAt.differentiableWithinAt, ?_⟩
    have hlim : Tendsto (fun z : ℂ => A i i + z⁻¹ * g i z⁻¹)
        (Bornology.cobounded ℂ) (𝓝 (A i i)) := by
      have hg := (hga i).continuousAt.tendsto.comp hi
      simpa using (tendsto_const_nhds.add (hi.mul hg))
    apply hlim.congr'
    filter_upwards [hi.eventually (hφeq i), hnz] with z hz hzne
    dsimp [branch]
    rw [hz]
    field_simp
    ring
  · intro z hz
    have h := hR ((le_max_left R 1).trans hz.le)
    exact ⟨fun i => (h.1 i).2, h.2⟩

open scoped Matrix.Norms.L2Operator in
/-- In Stahl's sign convention, distinct real slopes yield a common exterior domain of distinct
holomorphic eigenvalues of `A - z B`, with `branchᵢ(z) + bᵢ z → Aᵢᵢ`. Hermitian symmetry is
unnecessary for this local construction at infinity. [Stahl2013, §§2–5]. -/
private theorem exists_exterior_eigenvalue_branches_sub_real_diagonal
    (b : n → ℝ) (hb : Function.Injective b) (A : Matrix n n ℂ) :
    ∃ R : ℝ, 0 < R ∧ ∃ branch : n → ℂ → ℂ,
      (∀ i, DifferentiableOn ℂ (branch i) {z | R < ‖z‖} ∧
        Tendsto (fun z => branch i z + (b i : ℂ) * z)
          (Bornology.cobounded ℂ) (𝓝 (A i i))) ∧
      ∀ z, R < ‖z‖ →
        (∀ i, branch i z ∈ spectrum ℂ (A - z • Matrix.diagonal (fun i => (b i : ℂ)))) ∧
        Function.Injective (fun i => branch i z) := by
  have hd : Function.Injective (fun i => -(b i : ℂ)) :=
    neg_injective.comp (Complex.ofReal_injective.comp hb)
  obtain ⟨R, hR, branch, hbranch, hspec⟩ :=
    exists_exterior_eigenvalue_branches_of_diagonal (fun i => -(b i : ℂ)) hd A
  refine ⟨R, hR, branch, ?_, ?_⟩
  · intro i
    refine ⟨(hbranch i).1, ?_⟩
    simpa only [mul_neg, sub_neg_eq_add, mul_comm] using (hbranch i).2
  · intro z hz
    have hD : (Matrix.diagonal (fun i => -(b i : ℂ)) : Matrix n n ℂ) =
        -Matrix.diagonal (fun i => (b i : ℂ)) := by
      ext i j
      by_cases hij : i = j <;> simp [hij]
    simpa only [hD, smul_neg, ← sub_eq_add_neg] using hspec z hz

end NLAlib

end

section

open Filter Complex

open scoped Matrix Topology ComplexConjugate

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Conjugating a spectral point gives a spectral point of the adjoint matrix. [Stahl2013, §§2–5].
-/
theorem conj_mem_spectrum_conjTranspose {M : Matrix n n ℂ} {w : ℂ}
    (hw : w ∈ spectrum ℂ M) : conj w ∈ spectrum ℂ Mᴴ := by
  rw [spectrum.mem_iff] at hw ⊢
  have heq : algebraMap ℂ (Matrix n n ℂ) (conj w) - Mᴴ =
      (algebraMap ℂ (Matrix n n ℂ) w - M)ᴴ := by
    simp [Algebra.algebraMap_eq_smul_one, Matrix.conjTranspose_smul]
  rw [heq, Matrix.isUnit_conjTranspose]
  exact hw

private theorem tendsto_branch_mul_inv {branch : ℂ → ℂ} {a b : ℂ}
    (h : Tendsto (fun z => branch z + b * z) (Bornology.cobounded ℂ) (𝓝 a)) :
    Tendsto (fun z => branch z * z⁻¹) (Bornology.cobounded ℂ) (𝓝 (-b)) := by
  have hi : Tendsto (fun z : ℂ => z⁻¹) (Bornology.cobounded ℂ) (𝓝 0) :=
    tendsto_inv₀_cobounded
  have ht : Tendsto (fun z => (branch z + b * z) * z⁻¹ - b)
      (Bornology.cobounded ℂ) (𝓝 (-b)) := by
    simpa using (h.mul hi).sub_const b
  apply ht.congr'
  filter_upwards [eventually_cobounded_le_norm (1 : ℝ)] with z hz
  have hzne : z ≠ 0 := by intro hzero; norm_num [hzero] at hz
  field_simp
  ring

open scoped Matrix.Norms.L2Operator in
/-- A complete exterior branch family of a Hermitian pencil is Schwarz-symmetric outside a
possibly larger disk. Distinct real asymptotic slopes determine the branch label, so no branch
symmetry is assumed. [Stahl2013, §§2–5]. -/
private theorem eventually_exterior_eigenvalue_branches_conj_eq
    {A : Matrix n n ℂ} (hA : A.IsHermitian) (b : n → ℝ)
    (hb : Function.Injective b) {R : ℝ} {branch : n → ℂ → ℂ}
    (hlim : ∀ i, Tendsto (fun z => branch i z + (b i : ℂ) * z)
      (Bornology.cobounded ℂ) (𝓝 (A i i)))
    (hspec : ∀ z, R < ‖z‖ →
      (∀ i, branch i z ∈ spectrum ℂ (A - z • Matrix.diagonal (fun i => (b i : ℂ)))) ∧
        Function.Injective (fun i => branch i z)) :
    ∀ᶠ z in Bornology.cobounded ℂ, ∀ i, branch i (conj z) = conj (branch i z) := by
  have hnorm (i : n) : Tendsto (fun z => branch i z * z⁻¹)
      (Bornology.cobounded ℂ) (𝓝 (-(b i : ℂ))) := tendsto_branch_mul_inv (hlim i)
  have href (i : n) : Tendsto (fun z => conj (branch i (conj z)) * z⁻¹)
      (Bornology.cobounded ℂ) (𝓝 (-(b i : ℂ))) := by
    have h := Complex.continuous_conj.continuousAt.tendsto.comp
      ((hnorm i).comp Complex.isometry_conj.antilipschitz.tendsto_cobounded)
    simpa [Function.comp_def] using h
  have hneq : ∀ i j, ∀ᶠ z in Bornology.cobounded ℂ,
      i ≠ j → conj (branch i (conj z)) ≠ branch j z := by
    intro i j
    by_cases hij : i = j
    · exact Eventually.of_forall (fun _ h => False.elim (h hij))
    · have hn : -(b i : ℂ) - -(b j : ℂ) ≠ 0 := by
        intro heq
        exact hij (hb (Complex.ofReal_injective (neg_injective (sub_eq_zero.mp heq))))
      filter_upwards [((href i).sub (hnorm j)).eventually_ne hn] with z hz _ heq
      exact hz (by rw [heq]; ring)
  have hneq' : ∀ᶠ z in Bornology.cobounded ℂ, ∀ i j,
      i ≠ j → conj (branch i (conj z)) ≠ branch j z := by
    simpa only [Filter.eventually_all] using hneq
  filter_upwards [hneq', (tendsto_norm_cobounded_atTop (E := ℂ)).eventually_gt_atTop R]
    with z hz hR i
  have hs := hspec z hR
  have hcR : R < ‖conj z‖ := by simpa using hR
  have hci := conj_mem_spectrum_conjTranspose ((hspec (conj z) hcR).1 i)
  have hstar : (A - conj z • Matrix.diagonal (fun i => (b i : ℂ)))ᴴ =
      A - z • Matrix.diagonal (fun i => (b i : ℂ)) := by
    have hD : (Matrix.diagonal (fun i => (b i : ℂ)) : Matrix n n ℂ).IsHermitian :=
      Matrix.isHermitian_diagonal_of_self_adjoint _ (by ext i; simp)
    simp [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, hA.eq, hD.eq]
  rw [hstar, spectrum_eq_range_of_injective_mem_spectrum _ _ hs.2 hs.1] at hci
  obtain ⟨j, hj⟩ := hci
  have hji : i = j := by
    by_contra hij
    exact hz i j hij hj.symm
  subst j
  simpa using (congrArg conj hj).symm

open scoped Matrix.Norms.L2Operator in
/-- Hermitian pencils with distinct real diagonal slopes admit exterior branches satisfying
Schwarz reflection on one common exterior domain. The branches and their symmetry are both
constructed, not assumed. [Stahl2013, §§2–5]. -/
theorem _root_.Matrix.IsHermitian.exists_exterior_branches_sub_diagonal_conj_eq
    {A : Matrix n n ℂ} (hA : A.IsHermitian)
    (b : n → ℝ) (hb : Function.Injective b) :
    ∃ R : ℝ, 0 < R ∧ ∃ branch : n → ℂ → ℂ,
      (∀ i, DifferentiableOn ℂ (branch i) {z | R < ‖z‖} ∧
        Tendsto (fun z => branch i z + (b i : ℂ) * z)
          (Bornology.cobounded ℂ) (𝓝 (A i i))) ∧
      (∀ z, R < ‖z‖ →
        (∀ i, branch i z ∈ spectrum ℂ (A - z • Matrix.diagonal (fun i => (b i : ℂ)))) ∧
          Function.Injective (fun i => branch i z)) ∧
      ∀ i z, R < ‖z‖ → branch i (conj z) = conj (branch i z) := by
  obtain ⟨R, hR, branch, hbranch, hspec⟩ :=
    exists_exterior_eigenvalue_branches_sub_real_diagonal b hb A
  have href := eventually_exterior_eigenvalue_branches_conj_eq hA b hb
    (fun i => (hbranch i).2) hspec
  obtain ⟨S, _, hS⟩ := Filter.hasBasis_cobounded_norm.eventually_iff.mp href
  refine ⟨max R S, hR.trans_le (le_max_left _ _), branch, ?_, ?_, ?_⟩
  · intro i
    exact ⟨(hbranch i).1.mono (fun z hz => (le_max_left R S).trans_lt hz), (hbranch i).2⟩
  · intro z hz
    exact hspec z ((le_max_left R S).trans_lt hz)
  · intro i z hz
    exact hS ((le_max_right R S).trans hz.le) i

end NLAlib

end
