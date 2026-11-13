/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Spectrum
public import Mathlib.Analysis.Matrix.Spectrum
public import NLAlib.Matrix.Perturbation.PencilRoots
public import NLAlib.Matrix.Perturbation.ExteriorEigenvalueBranches
public import NLAlib.ForMathlib.Analysis.Complex.Reflection

/-!
# Inverse branches and upper-half-plane root sums

The inverse pencil branches parametrize the same determinant zero set as its forward branches.
Ordering the real asymptotic slopes separates upper and lower roots and identifies their sum
with the analytic continuation used in the trace representation.

## Main results

* `Matrix.IsHermitian.exists_inversePencilUpperRootSum_extension`.
-/

@[expose] public section

section

open Filter

open scoped Matrix Topology

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

private theorem tendsto_affine_branch_ratio {f : ℂ → ℂ} {a d : ℂ}
    (h : Tendsto (fun z => f z - z * d) (Bornology.cobounded ℂ) (𝓝 a)) :
    Tendsto (fun z => f z * z⁻¹) (Bornology.cobounded ℂ) (𝓝 d) := by
  have hi : Tendsto (fun z : ℂ => z⁻¹) (Bornology.cobounded ℂ) (𝓝 0) :=
    tendsto_inv₀_cobounded
  have h' : Tendsto (fun z => (f z - z * d) * z⁻¹ + d)
      (Bornology.cobounded ℂ) (𝓝 d) := by
    simpa using (h.mul hi).add_const d
  apply h'.congr'
  filter_upwards [eventually_cobounded_le_norm (1 : ℝ)] with z hz
  have hzne : z ≠ 0 := by intro hzero; norm_num [hzero] at hz
  field_simp
  ring

private theorem tendsto_cobounded_of_affine_branch {f : ℂ → ℂ} {a d : ℂ}
    (hd : d ≠ 0)
    (h : Tendsto (fun z => f z - z * d) (Bornology.cobounded ℂ) (𝓝 a)) :
    Tendsto f (Bornology.cobounded ℂ) (Bornology.cobounded ℂ) := by
  have hq := tendsto_affine_branch_ratio h
  have hfi : Tendsto (fun z => (f z)⁻¹) (Bornology.cobounded ℂ) (𝓝 0) := by
    have hh : Tendsto (fun z => (f z * z⁻¹)⁻¹ * z⁻¹)
        (Bornology.cobounded ℂ) (𝓝 0) := by
      simpa using (hq.inv₀ hd).mul (tendsto_inv₀_cobounded (α := ℂ))
    apply hh.congr'
    filter_upwards [eventually_cobounded_le_norm (1 : ℝ)] with z hz
    have hzne : z ≠ 0 := by intro hzero; norm_num [hzero] at hz
    simp only [mul_inv_rev, inv_inv]
    calc
      z * (f z)⁻¹ * z⁻¹ = (f z)⁻¹ * (z * z⁻¹) := by ring
      _ = (f z)⁻¹ := by rw [mul_inv_cancel₀ hzne, mul_one]
  have hne : ∀ᶠ z in Bornology.cobounded ℂ, (f z)⁻¹ ≠ 0 := by
    filter_upwards [hq.eventually_ne hd] with z hz
    exact inv_ne_zero (by intro hf; exact hz (by simp [hf]))
  have hi := tendsto_inv₀_nhdsNE_zero.comp (tendsto_nhdsWithin_iff.mpr ⟨hfi, hne⟩)
  simpa only [Function.comp_def, inv_inv] using hi

/-- The inverse spectral pencil exchanges `z` with `λ + s z`. Multiplication by the invertible
diagonal matrix preserves singularity, so this equivalence does not require a choice of
eigenvectors or eigenvalue branches. [Stahl2013, §§2–5]. -/
private theorem mem_spectrum_inverse_diagonal_pencil_iff
    (A : Matrix n n ℂ) (b : n → ℝ) (s : ℝ)
    (hs : ∀ i, s ≠ b i) (u z : ℂ) :
    z ∈ spectrum ℂ
        (-(Matrix.diagonal (fun i => ((s - b i : ℝ) : ℂ)⁻¹) * A) +
          u • Matrix.diagonal (fun i => ((s - b i : ℝ) : ℂ)⁻¹)) ↔
      u - (s : ℂ) * z ∈ spectrum ℂ
        (A - z • Matrix.diagonal (fun i => (b i : ℂ))) := by
  classical
  let D : Matrix n n ℂ := Matrix.diagonal (fun i => ((s - b i : ℝ) : ℂ))
  let E : Matrix n n ℂ := Matrix.diagonal (fun i => ((s - b i : ℝ) : ℂ)⁻¹)
  have hc : ∀ i, ((s - b i : ℝ) : ℂ) ≠ 0 := by
    intro i
    exact_mod_cast sub_ne_zero.mpr (hs i)
  have hDE : D * E = 1 := by
    dsimp only [D, E]
    rw [Matrix.diagonal_mul_diagonal]
    simpa only [mul_inv_cancel₀ (hc _)] using (Matrix.diagonal_one :
      (Matrix.diagonal (fun _ : n => (1 : ℂ))) = 1)
  have hD : IsUnit D := by
    apply (Matrix.isUnit_iff_isUnit_det D).mpr
    dsimp only [D]
    rw [Matrix.det_diagonal]
    exact isUnit_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr (fun i _ => hc i))
  have heq : D * (algebraMap ℂ (Matrix n n ℂ) z - (-(E * A) + u • E)) =
      -(algebraMap ℂ (Matrix n n ℂ) (u - (s : ℂ) * z) -
        (A - z • Matrix.diagonal (fun i => (b i : ℂ)))) := by
    simp only [mul_sub, mul_add, mul_neg, mul_smul_comm,
      ← mul_assoc, hDE, one_mul, Algebra.algebraMap_eq_smul_one,
      mul_one]
    ext i j
    by_cases hij : i = j
    · subst j
      simp [D]
      ring
    · simp [D, hij]
  rw [spectrum.mem_iff, spectrum.mem_iff]
  change (¬ IsUnit (algebraMap ℂ (Matrix n n ℂ) z - (-(E * A) + u • E))) ↔ _
  rw [← Units.isUnit_units_mul hD.unit, IsUnit.unit_spec, heq]
  rw [IsUnit.neg_iff]

/-- Distinct real slopes, away from `s`, give all exterior inverse branches. The affine asymptote
is `(u - Aᵢᵢ) / (s - bᵢ)`, with the diagonal entry of `A` interpreted as a complex number. These
branches are constructed from the actual matrix pencil, rather than postulated as local inverses.
[Stahl2013, §§2–5]. -/
private theorem exists_exterior_inverse_eigenvalue_branches
    (A : Matrix n n ℂ) (b : n → ℝ) (hb : Function.Injective b)
    (s : ℝ) (hs : ∀ i, s ≠ b i) :
    ∃ R : ℝ, 0 < R ∧ ∃ branch : n → ℂ → ℂ,
      (∀ i, DifferentiableOn ℂ (branch i) {u | R < ‖u‖} ∧
        Tendsto (fun u => branch i u - u / ((s - b i : ℝ) : ℂ))
          (Bornology.cobounded ℂ) (𝓝 (-A i i / ((s - b i : ℝ) : ℂ)))) ∧
      ∀ u, R < ‖u‖ →
        (∀ i, u - (s : ℂ) * branch i u ∈ spectrum ℂ
          (A - branch i u • Matrix.diagonal (fun i => (b i : ℂ)))) ∧
        Function.Injective (fun i => branch i u) := by
  let E : Matrix n n ℂ := Matrix.diagonal (fun i => ((s - b i : ℝ) : ℂ)⁻¹)
  have hd : Function.Injective (fun i => ((s - b i : ℝ) : ℂ)⁻¹) := by
    intro i j hij
    apply hb
    have h := Complex.ofReal_injective (inv_injective hij)
    linarith
  obtain ⟨R, hR, branch, hbranch, hspec⟩ :=
    exists_exterior_eigenvalue_branches_of_diagonal
      (fun i => ((s - b i : ℝ) : ℂ)⁻¹) hd (-(E * A))
  refine ⟨R, hR, branch, ?_, ?_⟩
  · intro i
    refine ⟨(hbranch i).1, ?_⟩
    simpa only [div_eq_mul_inv, Matrix.neg_apply, Matrix.diagonal_mul, E, neg_mul, mul_neg,
      mul_comm]
      using (hbranch i).2
  · intro u hu
    exact ⟨fun i => (mem_spectrum_inverse_diagonal_pencil_iff A b s hs u _).mp
      ((hspec u hu).1 i), (hspec u hu).2⟩

/-- The affine asymptotes match an inverse branch to its original exterior eigenvalue branch. In
particular, the index is determined by the distinct slopes, not by making an arbitrary spectral
choice at each parameter. [Stahl2013, §§2–5]. -/
theorem eventually_inverse_branches_eq
    (A : Matrix n n ℂ) (b : n → ℝ) (hb : Function.Injective b)
    (s : ℝ) (hs : ∀ i, s ≠ b i)
    {R S : ℝ} {forward inverse : n → ℂ → ℂ}
    (hforward : ∀ i, Tendsto (fun z => forward i z + (b i : ℂ) * z)
      (Bornology.cobounded ℂ) (𝓝 (A i i)))
    (hforwardSpec : ∀ z, R < ‖z‖ →
      (∀ i, forward i z ∈ spectrum ℂ
        (A - z • Matrix.diagonal (fun i => (b i : ℂ)))) ∧
      Function.Injective (fun i => forward i z))
    (hinverse : ∀ i, Tendsto (fun u => inverse i u - u / ((s - b i : ℝ) : ℂ))
      (Bornology.cobounded ℂ) (𝓝 (-A i i / ((s - b i : ℝ) : ℂ))))
    (hinverseSpec : ∀ u, S < ‖u‖ → ∀ i,
      u - (s : ℂ) * inverse i u ∈ spectrum ℂ
        (A - inverse i u • Matrix.diagonal (fun i => (b i : ℂ)))) :
    ∀ᶠ u in Bornology.cobounded ℂ,
      ∀ i, forward i (inverse i u) + (s : ℂ) * inverse i u = u := by
  have hc (i : n) : ((s - b i : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast sub_ne_zero.mpr (hs i)
  have hiratio (i : n) : Tendsto (fun u => inverse i u * u⁻¹)
      (Bornology.cobounded ℂ) (𝓝 (((s - b i : ℝ) : ℂ)⁻¹)) := by
    exact tendsto_affine_branch_ratio (by simpa only [div_eq_mul_inv] using hinverse i)
  have hicob (i : n) : Tendsto (inverse i) (Bornology.cobounded ℂ)
      (Bornology.cobounded ℂ) := by
    exact tendsto_cobounded_of_affine_branch (inv_ne_zero (hc i))
      (by simpa only [div_eq_mul_inv] using hinverse i)
  have hneq : ∀ i j, ∀ᶠ u in Bornology.cobounded ℂ,
      i ≠ j → u - (s : ℂ) * inverse i u ≠ forward j (inverse i u) := by
    intro i j
    by_cases hij : i = j
    · exact Eventually.of_forall (fun _ h => False.elim (h hij))
    have hres : Tendsto
        (fun u => (forward j (inverse i u) + (b j : ℂ) * inverse i u) * u⁻¹)
        (Bornology.cobounded ℂ) (𝓝 0) := by
      simpa using ((hforward j).comp (hicob i)).mul
        (tendsto_inv₀_cobounded (α := ℂ))
    have hlim : Tendsto
        (fun u => (u - (s : ℂ) * inverse i u - forward j (inverse i u)) * u⁻¹)
        (Bornology.cobounded ℂ)
        (𝓝 (1 + ((b j : ℂ) - (s : ℂ)) * ((s - b i : ℝ) : ℂ)⁻¹)) := by
      have hh := ((hiratio i).const_mul ((b j : ℂ) - (s : ℂ))).const_add 1 |>.sub hres
      simp only [sub_zero] at hh
      apply hh.congr'
      filter_upwards [eventually_cobounded_le_norm (1 : ℝ)] with u hu
      have hune : u ≠ 0 := by intro hzero; norm_num [hzero] at hu
      field_simp
      ring
    have hlimne : 1 + ((b j : ℂ) - (s : ℂ)) * ((s - b i : ℝ) : ℂ)⁻¹ ≠ 0 := by
      intro heq
      have hne : (b j : ℂ) ≠ (b i : ℂ) := by
        intro heq'
        exact hij (hb (Complex.ofReal_injective heq'.symm))
      apply hne
      have hc' := hc i
      push_cast at heq hc'
      field_simp at heq
      linear_combination heq
    filter_upwards [hlim.eventually_ne hlimne] with u hu _ heq
    exact hu (by rw [sub_eq_zero.mpr heq, zero_mul])
  have hneq' : ∀ᶠ u in Bornology.cobounded ℂ, ∀ i j,
      i ≠ j → u - (s : ℂ) * inverse i u ≠ forward j (inverse i u) := by
    simpa only [Filter.eventually_all] using hneq
  have hlarge : ∀ᶠ u in Bornology.cobounded ℂ, ∀ i, R < ‖inverse i u‖ := by
    simp only [Filter.eventually_all]
    intro i
    exact ((tendsto_norm_cobounded_atTop (E := ℂ)).comp (hicob i)).eventually_gt_atTop R
  filter_upwards [hneq', hlarge,
    (tendsto_norm_cobounded_atTop (E := ℂ)).eventually_gt_atTop S] with u hne hR hS i
  have hmem := hinverseSpec u hS i
  have hspec := hforwardSpec (inverse i u) (hR i)
  rw [spectrum_eq_range_of_injective_mem_spectrum _ _ hspec.2 hspec.1] at hmem
  obtain ⟨j, hj⟩ := hmem
  have hji : i = j := by
    by_contra hij
    exact hne i j hij hj.symm
  subst j
  linear_combination hj

end NLAlib

end

section

open Complex Filter

open scoped Matrix Topology

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

open scoped Matrix.Norms.L2Operator in
private theorem inverse_branch_im_ne_zero {A : Matrix n n ℂ} (hA : A.IsHermitian)
    (b : n → ℝ) (s : ℝ) {u z : ℂ} (hu : 0 < u.im)
    (hmem : u - (s : ℂ) * z ∈ spectrum ℂ
      (A - z • Matrix.diagonal (fun i => (b i : ℂ)))) : z.im ≠ 0 := by
  intro hzim
  have hzreal : (z.re : ℂ) = z := by
    apply Complex.ext <;> simp [hzim]
  have hB : (Matrix.diagonal (fun i => (b i : ℂ))).IsHermitian := by
    rw [Matrix.isHermitian_diagonal_iff]
    intro i
    simp [IsSelfAdjoint]
  have hreal : (A - z • Matrix.diagonal (fun i => (b i : ℂ))).IsHermitian := by
    rw [← hzreal]
    exact hA.sub (hB.smul (by simp [IsSelfAdjoint]))
  have him := hreal.isSelfAdjoint.im_eq_zero_of_mem_spectrum hmem
  have huim : u.im = 0 := by simpa [hzim] using him
  exact (ne_of_gt hu) huim

/-- For Hermitian `A`, the constructed exterior inverse branches are in the upper half-plane
precisely for indices with `bᵢ < s`. [Stahl2013, §§2–5]. -/
private theorem exists_exterior_inverse_eigenvalue_branches_im_pos_iff
    {A : Matrix n n ℂ} (hA : A.IsHermitian) (b : n → ℝ)
    (hb : Function.Injective b) (s : ℝ) (hs : ∀ i, s ≠ b i) :
    ∃ R : ℝ, 0 < R ∧ ∃ branch : n → ℂ → ℂ,
      (∀ i, DifferentiableOn ℂ (branch i) {u | R < ‖u‖} ∧
        Tendsto (fun u => branch i u - u / ((s - b i : ℝ) : ℂ))
          (Bornology.cobounded ℂ) (𝓝 (-A i i / ((s - b i : ℝ) : ℂ)))) ∧
      (∀ u, R < ‖u‖ →
        (∀ i, u - (s : ℂ) * branch i u ∈ spectrum ℂ
          (A - branch i u • Matrix.diagonal (fun i => (b i : ℂ)))) ∧
        Function.Injective (fun i => branch i u)) ∧
      ∀ u, R < ‖u‖ → 0 < u.im → ∀ i, 0 < (branch i u).im ↔ b i < s := by
  obtain ⟨R, hR, branch, hbranch, hspec⟩ :=
    exists_exterior_inverse_eigenvalue_branches A b hb s hs
  refine ⟨R, hR, branch, hbranch, hspec, ?_⟩
  intro u hu him i
  have hreal : ∀ v, R < ‖v‖ → 0 < v.im → (branch i v).im ≠ 0 := by
    intro v hv hvi
    exact inverse_branch_im_ne_zero hA b s hvi ((hspec v hv).1 i)
  have hlim : Tendsto (fun v => branch i v - (((s - b i)⁻¹ : ℝ) : ℂ) * v)
      (Bornology.cobounded ℂ) (𝓝 (-A i i / ((s - b i : ℝ) : ℂ))) := by
    simpa only [Complex.ofReal_inv, div_eq_mul_inv, mul_comm] using (hbranch i).2
  simpa only [inv_pos, sub_pos] using
    Complex.im_pos_iff_slope_pos_of_tendsto_affine
      (hbranch i).1.continuousOn hreal hlim (inv_ne_zero (sub_ne_zero.mpr (hs i))) hu him

end NLAlib

end

section

open Complex Filter

open scoped Matrix Topology ComplexConjugate

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

open scoped Matrix.Norms.L2Operator in
/-- A complete inverse branch family of a Hermitian diagonal pencil eventually satisfies Schwarz
reflection label by label. Its inverse matrix itself need not be Hermitian: the proof uses the
equivalent forward spectral equation. [Stahl2013, §§2–5]. -/
private theorem eventually_exterior_inverse_eigenvalue_branches_conj_eq
    {A : Matrix n n ℂ} (hA : A.IsHermitian) (b : n → ℝ)
    (hb : Function.Injective b) (s : ℝ) (hs : ∀ i, s ≠ b i)
    {R : ℝ} {branch : n → ℂ → ℂ}
    (hlim : ∀ i, Tendsto (fun u => branch i u - u / ((s - b i : ℝ) : ℂ))
      (Bornology.cobounded ℂ) (𝓝 (-A i i / ((s - b i : ℝ) : ℂ))))
    (hspec : ∀ u, R < ‖u‖ →
      (∀ i, u - (s : ℂ) * branch i u ∈ spectrum ℂ
        (A - branch i u • Matrix.diagonal (fun i => (b i : ℂ)))) ∧
      Function.Injective (fun i => branch i u)) :
    ∀ᶠ u in Bornology.cobounded ℂ, ∀ i, branch i (conj u) = conj (branch i u) := by
  let d : n → ℝ := fun i => (s - b i)⁻¹
  have hd : Function.Injective d := by
    intro i j hij
    apply hb
    have heq := inv_injective hij
    linarith
  apply Complex.eventually_conj_eq_of_tendsto_affine_of_finite_matching
    branch d (fun i => -A i i / ((s - b i : ℝ) : ℂ)) hd
  · intro i
    simpa only [d, Complex.ofReal_inv, div_eq_mul_inv, mul_comm] using hlim i
  filter_upwards [(tendsto_norm_cobounded_atTop (E := ℂ)).eventually_gt_atTop R]
    with u hu i
  let M : Matrix n n ℂ :=
    -(Matrix.diagonal (fun i => ((s - b i : ℝ) : ℂ)⁻¹) * A) +
      u • Matrix.diagonal (fun i => ((s - b i : ℝ) : ℂ)⁻¹)
  have hM : ∀ j, branch j u ∈ spectrum ℂ M := fun j =>
    (mem_spectrum_inverse_diagonal_pencil_iff A b s hs u _).mpr ((hspec u hu).1 j)
  have hconjR : R < ‖conj u‖ := by simpa only [norm_conj] using hu
  have hc := conj_mem_spectrum_conjTranspose ((hspec (conj u) hconjR).1 i)
  have hD : (Matrix.diagonal (fun i => (b i : ℂ)) : Matrix n n ℂ).IsHermitian :=
    Matrix.isHermitian_diagonal_of_self_adjoint _ (by ext i; simp)
  have hstar : (A - branch i (conj u) • Matrix.diagonal (fun i => (b i : ℂ)))ᴴ =
      A - conj (branch i (conj u)) • Matrix.diagonal (fun i => (b i : ℂ)) := by
    simp [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, hA.eq, hD.eq]
  rw [hstar] at hc
  have hc' : u - (s : ℂ) * conj (branch i (conj u)) ∈ spectrum ℂ
      (A - conj (branch i (conj u)) • Matrix.diagonal (fun i => (b i : ℂ))) := by
    simpa using hc
  have hmem : conj (branch i (conj u)) ∈ spectrum ℂ M :=
    (mem_spectrum_inverse_diagonal_pencil_iff A b s hs u _).mpr hc'
  rw [spectrum_eq_range_of_injective_mem_spectrum _ _ (hspec u hu).2 hM] at hmem
  obtain ⟨j, hj⟩ := hmem
  exact ⟨j, hj.symm⟩

open scoped Matrix.Norms.L2Operator in
/-- Constructed inverse branches of a Hermitian pencil have both the correct upper-half-plane
labels and Schwarz reflection on one common exterior domain. [Stahl2013, §§2–5]. -/
private theorem exists_exterior_inverse_eigenvalue_branches_im_pos_iff_conj_eq
    {A : Matrix n n ℂ} (hA : A.IsHermitian) (b : n → ℝ)
    (hb : Function.Injective b) (s : ℝ) (hs : ∀ i, s ≠ b i) :
    ∃ R : ℝ, 0 < R ∧ ∃ branch : n → ℂ → ℂ,
      (∀ i, DifferentiableOn ℂ (branch i) {u | R < ‖u‖} ∧
        Tendsto (fun u => branch i u - u / ((s - b i : ℝ) : ℂ))
          (Bornology.cobounded ℂ) (𝓝 (-A i i / ((s - b i : ℝ) : ℂ)))) ∧
      (∀ u, R < ‖u‖ →
        (∀ i, u - (s : ℂ) * branch i u ∈ spectrum ℂ
          (A - branch i u • Matrix.diagonal (fun i => (b i : ℂ)))) ∧
        Function.Injective (fun i => branch i u)) ∧
      (∀ u, R < ‖u‖ → 0 < u.im → ∀ i, 0 < (branch i u).im ↔ b i < s) ∧
      ∀ i u, R < ‖u‖ → branch i (conj u) = conj (branch i u) := by
  obtain ⟨R, hR, branch, hbranch, hspec, hlabel⟩ :=
    exists_exterior_inverse_eigenvalue_branches_im_pos_iff hA b hb s hs
  have href := eventually_exterior_inverse_eigenvalue_branches_conj_eq hA b hb s hs
    (fun i => (hbranch i).2) hspec
  obtain ⟨S, _, hS⟩ := Filter.hasBasis_cobounded_norm.eventually_iff.mp href
  refine ⟨max R S, hR.trans_le (le_max_left _ _), branch, ?_, ?_, ?_, ?_⟩
  · intro i
    exact ⟨(hbranch i).1.mono (fun u hu => (le_max_left R S).trans_lt hu), (hbranch i).2⟩
  · intro u hu
    exact hspec u ((le_max_left R S).trans_lt hu)
  · intro u hu him i
    exact hlabel u ((le_max_left R S).trans_lt hu) him i
  · intro i u hu
    exact hS ((le_max_right R S).trans hu.le) i

end NLAlib

end

section

open Complex Filter

open scoped Matrix Topology ComplexConjugate

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The diagonal slope matrix `diag (bᵢ - s)` is invertible when `s` avoids its finitely many
diagonal values. [Stahl2013, §§2–5]. -/
private theorem isUnit_diagonal_sub_of_ne (b : n → ℝ) (s : ℝ) (hs : ∀ i, s ≠ b i) :
    IsUnit (Matrix.diagonal (fun i => ((b i - s : ℝ) : ℂ))) := by
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  rw [Matrix.det_diagonal]
  apply isUnit_iff_ne_zero.mpr
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  exact_mod_cast sub_ne_zero.mpr (hs i).symm

/-- The inverse matrix of a diagonal Hermitian pencil is exactly the affine pencil used to
construct its exterior inverse branches. [Stahl2013, §§2–5]. -/
private theorem inv_mul_sub_smul_one_diagonal_eq (A : Matrix n n ℂ) (b : n → ℝ)
    (s : ℝ) (hs : ∀ i, s ≠ b i) (u : ℂ) :
    (Matrix.diagonal (fun i => ((b i - s : ℝ) : ℂ)))⁻¹ *
        (A - u • (1 : Matrix n n ℂ)) =
      -(Matrix.diagonal (fun i => ((s - b i : ℝ) : ℂ)⁻¹) * A) +
        u • Matrix.diagonal (fun i => ((s - b i : ℝ) : ℂ)⁻¹) := by
  let D : Matrix n n ℂ := Matrix.diagonal (fun i => ((b i - s : ℝ) : ℂ))
  let E : Matrix n n ℂ := Matrix.diagonal (fun i => ((s - b i : ℝ) : ℂ)⁻¹)
  have hc (i : n) : ((s - b i : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast sub_ne_zero.mpr (hs i)
  have hneg (i : n) : ((b i - s : ℝ) : ℂ) = -((s - b i : ℝ) : ℂ) := by
    push_cast
    ring
  have hDE : D * (-E) = 1 := by
    rw [Matrix.mul_neg]
    dsimp only [D, E]
    rw [Matrix.diagonal_mul_diagonal]
    have hentry : (fun i => ((b i - s : ℝ) : ℂ) * ((s - b i : ℝ) : ℂ)⁻¹) =
        fun _ => (-1 : ℂ) := by
      funext i
      rw [hneg, neg_mul, mul_inv_cancel₀ (hc i)]
    rw [hentry, ← Matrix.diagonal_neg]
    simp
  have hinv : D⁻¹ = -E := Matrix.inv_eq_right_inv hDE
  change D⁻¹ * (A - u • (1 : Matrix n n ℂ)) = -(E * A) + u • E
  rw [hinv, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one, Matrix.neg_mul, smul_neg]
  abel

/-- A complete exterior inverse branch family with the proved upper labels computes the actual
upper-root sum of the inverse characteristic polynomial. [Stahl2013, §§2–5]. -/
private theorem inversePencilUpperRootSum_eq_sum_ite_of_inverse_branches
    (A : Matrix n n ℂ) (b : n → ℝ) (s : ℝ) (hs : ∀ i, s ≠ b i)
    (branch : n → ℂ → ℂ) (u : ℂ)
    (hspec : ∀ i, u - (s : ℂ) * branch i u ∈ spectrum ℂ
      (A - branch i u • Matrix.diagonal (fun i => (b i : ℂ))))
    (hinj : Function.Injective (fun i => branch i u))
    (hlabel : ∀ i, 0 < (branch i u).im ↔ b i < s) :
    inversePencilUpperRootSum A (Matrix.diagonal (fun i => ((b i - s : ℝ) : ℂ))) u =
      ∑ i, if b i < s then branch i u else 0 := by
  classical
  let M : Matrix n n ℂ :=
    -(Matrix.diagonal (fun i => ((s - b i : ℝ) : ℂ)⁻¹) * A) +
      u • Matrix.diagonal (fun i => ((s - b i : ℝ) : ℂ)⁻¹)
  have hmem : ∀ i, branch i u ∈ spectrum ℂ M := fun i =>
    (mem_spectrum_inverse_diagonal_pencil_iff A b s hs u _).mpr (hspec i)
  unfold inversePencilUpperRootSum
  rw [inv_mul_sub_smul_one_diagonal_eq A b s hs u,
    Matrix.sum_filter_roots_charpoly_eq_sum_ite_of_injective_mem_spectrum M
      (fun i => branch i u) hinj hmem]
  apply Finset.sum_congr rfl
  intro i _
  simp only [hlabel i]

open scoped Matrix.Norms.L2Operator in
/-- One constructed family of exterior inverse branches supplies holomorphy, the complete spectral
list, the strict-sublevel labels, Schwarz reflection, and the identity with the actual upper-root
sum throughout the exterior upper half-plane. [Stahl2013, §§2–5]. -/
theorem _root_.Matrix.IsHermitian.exists_inverse_branches_root_sum
    {A : Matrix n n ℂ} (hA : A.IsHermitian) (b : n → ℝ)
    (hb : Function.Injective b) (s : ℝ) (hs : ∀ i, s ≠ b i) :
    ∃ R : ℝ, 0 < R ∧ ∃ branch : n → ℂ → ℂ,
      (∀ i, DifferentiableOn ℂ (branch i) {u | R < ‖u‖} ∧
        Tendsto (fun u => branch i u - u / ((s - b i : ℝ) : ℂ))
          (Bornology.cobounded ℂ) (𝓝 (-A i i / ((s - b i : ℝ) : ℂ)))) ∧
      (∀ u, R < ‖u‖ →
        (∀ i, u - (s : ℂ) * branch i u ∈ spectrum ℂ
          (A - branch i u • Matrix.diagonal (fun i => (b i : ℂ)))) ∧
        Function.Injective (fun i => branch i u)) ∧
      (∀ u, R < ‖u‖ → 0 < u.im → ∀ i, 0 < (branch i u).im ↔ b i < s) ∧
      (∀ i u, R < ‖u‖ → branch i (conj u) = conj (branch i u)) ∧
      ∀ u, R < ‖u‖ → 0 < u.im →
        inversePencilUpperRootSum A (Matrix.diagonal (fun i => ((b i - s : ℝ) : ℂ))) u =
          ∑ i, if b i < s then branch i u else 0 := by
  obtain ⟨R, hR, branch, hbranch, hspec, hlabel, href⟩ :=
    exists_exterior_inverse_eigenvalue_branches_im_pos_iff_conj_eq hA b hb s hs
  refine ⟨R, hR, branch, hbranch, hspec, hlabel, href, ?_⟩
  intro u hu him
  exact inversePencilUpperRootSum_eq_sum_ite_of_inverse_branches A b s hs branch u
    (hspec u hu).1 (hspec u hu).2 (hlabel u hu him)

end NLAlib

end

section

open Complex Set Filter

open scoped Matrix Topology ComplexConjugate

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Actual upper characteristic roots glue to a Schwarz-symmetric exterior inverse family on an
open slit-plane domain. The global bound includes the real points and therefore controls every
thin contour uniformly. [Stahl2013, §§2–5]. -/
theorem _root_.Matrix.IsHermitian.exists_inversePencilUpperRootSum_extension
    {A : Matrix n n ℂ} (hA : A.IsHermitian) (b : n → ℝ) (s : ℝ)
    (hs : ∀ i, s ≠ b i) {R : ℝ} (branch : n → ℂ → ℂ)
    (hdiff : ∀ i, DifferentiableOn ℂ (branch i) {u | R < ‖u‖})
    (hspec : ∀ u, R < ‖u‖ → ∀ i, u - (s : ℂ) * branch i u ∈ spectrum ℂ
      (A - branch i u • Matrix.diagonal (fun i => (b i : ℂ))))
    (hroot : ∀ u, R < ‖u‖ → 0 < u.im →
      inversePencilUpperRootSum A (Matrix.diagonal (fun i => ((b i - s : ℝ) : ℂ))) u =
        ∑ i, if b i < s then branch i u else 0)
    (href : ∀ i u, R < ‖u‖ → branch i (conj u) = conj (branch i u)) :
    ∃ h : ℂ → ℂ,
      DifferentiableOn ℂ h ({u | u.im ≠ 0} ∪ {u | R < ‖u‖}) ∧
      (∀ u, R < ‖u‖ → h u = ∑ i, if b i < s then branch i u else 0) ∧
      (∀ u, 0 < u.im → h u =
        inversePencilUpperRootSum A (Matrix.diagonal (fun i => ((b i - s : ℝ) : ℂ))) u) ∧
      (∀ u, h (conj u) = conj (h u)) ∧
      (∀ u, 0 < u.im → 0 ≤ (h u).im) ∧
      ∀ u, ‖h u‖ ≤ (Fintype.card n : ℝ) *
        specNorm (Matrix.diagonal (fun i => ((b i - s : ℝ) : ℂ)))⁻¹ *
          (specNorm A + ‖u‖) := by
  classical
  let D : Matrix n n ℂ := Matrix.diagonal (fun i => ((b i - s : ℝ) : ℂ))
  let f := inversePencilUpperRootSum A D
  let g : ℂ → ℂ := fun u => ∑ i, if b i < s then branch i u else 0
  let axis : ℂ → ℂ := fun u => if R < ‖u‖ then g u else 0
  let h := schwarzHalfPlaneExtension f axis
  have hDu : IsUnit D := isUnit_diagonal_sub_of_ne b s hs
  have hD : D.IsHermitian :=
    Matrix.isHermitian_diagonal_of_self_adjoint _ (by ext i; simp)
  have hf : ∀ u : ℂ, 0 < u.im → DifferentiableAt ℂ f u := by
    intro u hu
    exact (Matrix.IsHermitian.analyticAt_inversePencilUpperRootSum hA hD hDu
      (ne_of_gt hu)).differentiableAt
  have hg : DifferentiableOn ℂ g {u | R < ‖u‖} := by
    apply DifferentiableOn.fun_sum
    intro i _
    by_cases hi : b i < s
    · simpa only [if_pos hi] using hdiff i
    · simpa only [if_neg hi] using (differentiableOn_const (𝕜 := ℂ) (0 : ℂ) :
        DifferentiableOn ℂ (fun _ : ℂ => (0 : ℂ)) {u | R < ‖u‖})
  have haxis : DifferentiableOn ℂ axis {u | R < ‖u‖} := by
    apply hg.congr
    intro u hu
    change R < ‖u‖ at hu
    simp only [axis, if_pos hu]
  have hupp : ∀ u : ℂ, R < ‖u‖ → 0 < u.im → f u = axis u := by
    intro u hu him
    simpa only [axis, if_pos hu] using hroot u hu him
  have hrefg : ∀ u : ℂ, R < ‖u‖ → g (conj u) = conj (g u) := by
    intro u hu
    simp only [g, map_sum]
    apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> simp [href i u hu]
  have hrefaxis : ∀ u : ℂ, R < ‖u‖ → axis (conj u) = conj (axis u) := by
    intro u hu
    simpa only [axis, norm_conj, if_pos hu] using hrefg u hu
  have hrefaxisall (u : ℂ) : axis (conj u) = conj (axis u) := by
    by_cases hu : R < ‖u‖
    · exact hrefaxis u hu
    · simp only [axis, norm_conj, if_neg hu, map_zero]
  have hgnorm (u : ℂ) (hu : R < ‖u‖) : ‖g u‖ ≤
      (Fintype.card n : ℝ) * specNorm D⁻¹ * (specNorm A + ‖u‖) := by
    apply norm_sum_ite_le_card_mul_specNorm_inv_of_det_pencil_eq_zero A D hDu u
      (fun i => branch i u)
    intro i
    apply (det_smul_one_sub_add_smul_eq_zero_iff_mem_spectrum_inv_mul A D hDu u _).mpr
    dsimp only [D]
    rw [inv_mul_sub_smul_one_diagonal_eq A b s hs u]
    exact (mem_spectrum_inverse_diagonal_pencil_iff A b s hs u _).mpr (hspec u hu i)
  refine ⟨h, differentiableOn_schwarzHalfPlaneExtension_union_exterior f axis hf haxis hupp
    hrefaxis, ?_, ?_, schwarzHalfPlaneExtension_conj_of_conj_eq_axis f axis hrefaxisall, ?_, ?_⟩
  · intro u hu
    simpa only [axis, if_pos hu] using
      schwarzHalfPlaneExtension_eq_of_conj_eq f axis hupp hrefaxis hu
  · intro u hu
    simp only [h, schwarzHalfPlaneExtension, if_pos hu]
    rfl
  · intro u hu
    simpa only [h, schwarzHalfPlaneExtension, if_pos hu] using
      inversePencilUpperRootSum_im_nonneg A D u
  · intro u
    have hC : 0 ≤ (Fintype.card n : ℝ) * specNorm D⁻¹ * (specNorm A + ‖u‖) :=
      mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (specNorm_nonneg _))
        (add_nonneg (specNorm_nonneg _) (norm_nonneg _))
    dsimp only [h, schwarzHalfPlaneExtension]
    split_ifs with hpos hneg
    · exact norm_inversePencilUpperRootSum_le A D hDu u
    · simpa only [norm_conj] using norm_inversePencilUpperRootSum_le A D hDu (conj u)
    · dsimp only [axis]
      split_ifs with hu
      · exact hgnorm u hu
      · simpa only [norm_zero] using hC

end NLAlib

end
