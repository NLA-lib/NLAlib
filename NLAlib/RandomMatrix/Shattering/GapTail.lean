/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.RandomMatrix.Shattering.ConditionTail
public import NLAlib.Matrix.Perturbation.EigenvalueClustering
public import NLAlib.Matrix.QRIteration.SquareGrid

/-!
# Eigenvalue gap of a Ginibre perturbation

For a deterministic complex matrix $\mathbf{M}$ of order $n$, $\gamma > 0$ and a standard
complex Gaussian matrix $\mathbf{G}$ (independent entries of mean square modulus one), the
eigenvalues of $\mathbf{M} + \gamma n^{-1/2}\mathbf{G}$ admit a listing with all distinct-index
gaps above $t$ except with probability
$10000e\,n^5\sqrt{t/\gamma}\,(\|\mathbf{M}\|_2/\gamma + \log(\gamma/t))^2$: the eigenvalue half
of pseudospectral shattering [BanksGarzaVargasKulkarniSrivastava2020].

Two eigenvalues within $r$ of a point $y$ force the second-smallest singular value of
$y\mathbf{I} - \mathbf{A}$ below $r$ times the condition number of a diagonalizer
(`NLAlib.exists_mem_singularValues_le_of_not_exists_isEigenvalueListing`). A disk net of
$36(R/r)^2$ points, the fourth-power tail of the second-smallest singular value, the condition
tail of `NLAlib.RandomMatrix.Shattering.ConditionTail` and the norm cutoff
`NLAlib.measureReal_specNorm_add_smul_ge_mul_le_of_hasLaw_complexGaussianMatrix` combine at
$r = t$, condition cutoff $(\gamma/t)^{1/4}$ and disk radius
$3\gamma(\|\mathbf{M}\|_2/\gamma + \log(\gamma/t))$.

## Main results

* `NLAlib.measureReal_not_exists_isEigenvalueListing_le_le_log_sq_of_hasLaw_complexGaussianMatrix`:
  the gap tail with constants $(10000e, 5, 1/2, 2)$.
* `exists_forall_measureReal_not_exists_isEigenvalueListing_le_of_hasLaw_complexGaussianMatrix`:
  its asymptotic form.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

private theorem measureReal_exists_mem_singularValues_le_le
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {G : Ω → Matrix n n ℂ}
    (hG : HasLaw G (complexGaussianMatrix n n) μ) (M : Matrix n n ℂ)
    {k : ℕ} (hk : k + 2 = Fintype.card n) {γ x : ℝ} (hγ : 0 < γ) (hx : 0 ≤ x)
    (Z : Finset ℂ) :
    μ.real {ω | ∃ y ∈ Z,
      singularValues (y • 1 - (M + (γ / √(Fintype.card n : ℝ)) • G ω)) k ≤ x} ≤
      (Z.card : ℝ) * (Fintype.card n : ℝ) ^ 5 * (x / γ) ^ 4 := by
  have : IsProbabilityMeasure μ := hG.isProbabilityMeasure_iff.2 inferInstance
  have heq : {ω | ∃ y ∈ Z,
      singularValues (y • 1 - (M + (γ / √(Fintype.card n : ℝ)) • G ω)) k ≤ x} =
      ⋃ y : Z, {ω | singularValues ((y : ℂ) • 1 -
        (M + (γ / √(Fintype.card n : ℝ)) • G ω)) k ≤ x} := by
    ext ω
    simp
  rw [heq]
  calc
    _ ≤ ∑ y : Z, μ.real {ω | singularValues ((y : ℂ) • 1 -
        (M + (γ / √(Fintype.card n : ℝ)) • G ω)) k ≤ x} :=
      measureReal_iUnion_fintype_le _
    _ ≤ ∑ _y : Z, (Fintype.card n : ℝ) ^ 5 * (x / γ) ^ 4 := by
      apply Finset.sum_le_sum
      intro y _
      have he (ω : Ω) : (y : ℂ) • (1 : Matrix n n ℂ) -
          (M + (γ / √(Fintype.card n : ℝ)) • G ω) =
          -(M - (y : ℂ) • 1 + (γ / √(Fintype.card n : ℝ)) • G ω) := by abel
      simp_rw [he, singularValues_neg]
      exact measureReal_singularValues_add_smul_le_le_pow_four_of_hasLaw_complexGaussianMatrix
        hG _ hk hγ hx
    _ = _ := by simp [mul_assoc]

private theorem measureReal_gap_le_cutoff
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {G : Ω → Matrix n n ℂ}
    (hG : HasLaw G (complexGaussianMatrix n n) μ) (M : Matrix n n ℂ)
    {k : ℕ} (hk : k + 2 = Fintype.card n) {γ r R B : ℝ}
    (hγ : 0 < γ) (hr : 0 < r) (hR : 0 < R) (hrR : r ≤ R) (hB : 0 < B) :
    μ.real {ω | ¬ ∃ d : n → ℂ,
      IsEigenvalueListing (M + (γ / √(Fintype.card n : ℝ)) • G ω) d ∧
        ∀ i j, i ≠ j → r < ‖d i - d j‖} ≤
      μ.real {ω | ¬ ∃ (V : Matrix n n ℂ) (d : n → ℂ), IsUnit V ∧
        (M + (γ / √(Fintype.card n : ℝ)) • G ω) * V = V * Matrix.diagonal d ∧
          pseudoConditionNumber V ≤ B} +
      μ.real {ω | R ≤ specNorm (M + (γ / √(Fintype.card n : ℝ)) • G ω)} +
      (36 * R ^ 2 / r ^ 2) * (Fintype.card n : ℝ) ^ 5 * (2 * r * B / γ) ^ 4 := by
  have : IsProbabilityMeasure μ := hG.isProbabilityMeasure_iff.2 inferInstance
  obtain ⟨Z, hcard, hZ⟩ := exists_finset_card_mul_sq_le_and_forall_norm_sub_le 0 hR hr hrR
  simp only [sub_zero] at hZ
  let S := {ω | ¬ ∃ (V : Matrix n n ℂ) (d : n → ℂ), IsUnit V ∧
    (M + (γ / √(Fintype.card n : ℝ)) • G ω) * V = V * Matrix.diagonal d ∧
      pseudoConditionNumber V ≤ B}
  let T := {ω | R ≤ specNorm (M + (γ / √(Fintype.card n : ℝ)) • G ω)}
  let U := {ω | ∃ y ∈ Z, singularValues (y • 1 -
    (M + (γ / √(Fintype.card n : ℝ)) • G ω)) k ≤ 2 * r * B}
  have hsub : {ω | ¬ ∃ d : n → ℂ,
      IsEigenvalueListing (M + (γ / √(Fintype.card n : ℝ)) • G ω) d ∧
        ∀ i j, i ≠ j → r < ‖d i - d j‖} ⊆ (S ∪ T) ∪ U := by
    intro ω hω
    by_cases hS : ω ∈ S
    · exact Or.inl (Or.inl hS)
    by_cases hT : ω ∈ T
    · exact Or.inl (Or.inr hT)
    right
    obtain ⟨V, d, hV, hAV, hVB⟩ := not_not.mp hS
    exact exists_mem_singularValues_le_of_not_exists_isEigenvalueListing hV hAV hk hr
      (lt_of_not_ge hT) hVB Z hZ hω
  have hcount : (Z.card : ℝ) ≤ 36 * R ^ 2 / r ^ 2 :=
    (le_div_iff₀ (sq_pos_of_pos hr)).2 hcard
  calc
    _ ≤ μ.real ((S ∪ T) ∪ U) := measureReal_mono hsub
    _ ≤ μ.real (S ∪ T) + μ.real U := measureReal_union_le _ _
    _ ≤ μ.real S + μ.real T + μ.real U := by
      exact add_le_add (measureReal_union_le S T) le_rfl
    _ ≤ μ.real S + μ.real T +
        (Z.card : ℝ) * (Fintype.card n : ℝ) ^ 5 * (2 * r * B / γ) ^ 4 := by
      exact add_le_add le_rfl
        (measureReal_exists_mem_singularValues_le_le hG M hk hγ (x := 2 * r * B)
          (by positivity) Z)
    _ ≤ _ := by gcongr

private theorem gap_tail_combine {N K τ R γ q : ℝ}
    (hN : 1 ≤ N) (hK : 2 ≤ K) (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (hγ : 0 < γ) (hR : 0 ≤ R) (hRupper : R ≤ 3 * γ * K)
    (hq : 0 < q) (hq4 : q ^ 4 = τ) :
    128 * Real.exp 1 * N ^ 3 * √τ * K ^ 2 + τ ^ 2 +
        (36 * R ^ 2 / (γ * τ) ^ 2) * N ^ 5 * (2 * (γ * τ) * q⁻¹ / γ) ^ 4 ≤
      (10000 * Real.exp 1) * N ^ 5 * √τ * K ^ 2 := by
  have hτsqrt : τ ≤ √τ := Real.le_sqrt_self_iff.mpr hτ1
  have hτ2 : τ ^ 2 ≤ √τ := (by nlinarith : τ ^ 2 ≤ τ).trans hτsqrt
  have hnet : (36 * R ^ 2 / (γ * τ) ^ 2) * N ^ 5 *
      (2 * (γ * τ) * q⁻¹ / γ) ^ 4 = 576 * N ^ 5 * (R / γ) ^ 2 * τ := by
    field_simp
    rw [hq4]
    ring
  rw [hnet]
  have hRdiv : R / γ ≤ 3 * K := by
    rw [div_le_iff₀ hγ]
    nlinarith
  have hRdiv0 : 0 ≤ R / γ := by positivity
  have hnetle : 576 * N ^ 5 * (R / γ) ^ 2 * τ ≤ 5184 * N ^ 5 * √τ * K ^ 2 := by
    calc
      _ ≤ 576 * N ^ 5 * (3 * K) ^ 2 * √τ := by gcongr
      _ = _ := by ring
  have hn35 : N ^ 3 ≤ N ^ 5 := pow_le_pow_right₀ hN (by norm_num)
  have hκ : 128 * Real.exp 1 * N ^ 3 * √τ * K ^ 2 ≤
      128 * Real.exp 1 * N ^ 5 * √τ * K ^ 2 := by gcongr
  have hNK : 1 ≤ N ^ 5 * K ^ 2 :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ hN) (by nlinarith)
  have hrest : τ ^ 2 ≤ N ^ 5 * √τ * K ^ 2 := by
    calc
      _ ≤ √τ := hτ2
      _ ≤ (N ^ 5 * K ^ 2) * √τ := le_mul_of_one_le_left (by positivity) hNK
      _ = _ := by ring
  have he : 1 ≤ Real.exp 1 := Real.one_le_exp_iff.mpr (by norm_num)
  have hprod : 0 ≤ N ^ 5 * √τ * K ^ 2 := by positivity
  nlinarith [mul_le_mul_of_nonneg_right he hprod]

private theorem measureReal_gap_le_log_sq_of_card_eq_add_two
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {G : Ω → Matrix n n ℂ}
    (hG : HasLaw G (complexGaussianMatrix n n) μ) (M : Matrix n n ℂ)
    {k : ℕ} (hk : k + 2 = Fintype.card n) {γ r : ℝ}
    (hγ : 0 < γ) (hγM : 2 * γ ≤ specNorm M) (hr : 0 < r) (hrγ : r ≤ γ) :
    μ.real {ω | ¬ ∃ d : n → ℂ,
      IsEigenvalueListing (M + (γ / √(Fintype.card n : ℝ)) • G ω) d ∧
        ∀ i j, i ≠ j → r < ‖d i - d j‖} ≤
      (10000 * Real.exp 1) * (Fintype.card n : ℝ) ^ 5 * √(r / γ) *
        (specNorm M / γ + Real.log (r / γ)⁻¹) ^ 2 := by
  let τ := r / γ
  let q := √(√τ)
  let L := Real.log τ⁻¹
  let K := specNorm M / γ + L
  let R := 3 * γ * K
  have hτ : 0 < τ := by dsimp [τ]; positivity
  have hτ1 : τ ≤ 1 := (div_le_one hγ).2 hrγ
  have hq : 0 < q := by dsimp [q]; positivity
  have hq1 : q ≤ 1 := Real.sqrt_le_one.mpr (Real.sqrt_le_one.mpr hτ1)
  have hτq : τ ≤ q := (Real.le_sqrt_self_iff.mpr hτ1).trans
    (Real.le_sqrt_self_iff.mpr (Real.sqrt_le_one.mpr hτ1))
  have hq2 : q ^ 2 = √τ := Real.sq_sqrt (Real.sqrt_nonneg _)
  have hq4 : q ^ 4 = τ := by
    rw [show 4 = 2 * 2 by norm_num, pow_mul, hq2, Real.sq_sqrt hτ.le]
  have hL : 0 ≤ L := Real.log_nonneg ((one_le_inv₀ hτ).2 hτ1)
  have hm : 2 ≤ specNorm M / γ := (le_div_iff₀ hγ).2 hγM
  have hK : 2 ≤ K := by dsimp [K]; linarith
  have hn : (1 : ℝ) ≤ Fintype.card n := by
    exact_mod_cast (show 1 ≤ Fintype.card n by omega)
  have hR : 0 < R := mul_pos (by positivity) (by linarith)
  have hlog : Real.log q⁻¹ ≤ L :=
    Real.log_le_log (inv_pos.mpr hq) ((inv_le_inv₀ hq hτ).2 hτq)
  have hκ :=
    measureReal_not_exists_pseudoConditionNumber_le_le_log_sq_of_hasLaw_complexGaussianMatrix
    hG M hγ hγM hq hq1
  have hκbound : 128 * Real.exp 1 * (Fintype.card n : ℝ) ^ 3 * q ^ 2 *
      (specNorm M / γ + Real.log q⁻¹) ^ 2 ≤
      128 * Real.exp 1 * (Fintype.card n : ℝ) ^ 3 * √τ * K ^ 2 := by
    rw [hq2]
    have hlog0 : 0 ≤ Real.log q⁻¹ := Real.log_nonneg ((one_le_inv₀ hq).2 hq1)
    dsimp [K]
    gcongr
  have hκupper := hκ.trans hκbound
  have hnorm :=
    measureReal_specNorm_add_smul_ge_mul_le_of_hasLaw_complexGaussianMatrix hG M hγ hγM hτ hτ1
  have hrR : r ≤ R := by
    have hRM : R = 3 * specNorm M + 3 * γ * L := by
      dsimp [R, K]
      field_simp
    nlinarith [specNorm_nonneg M]
  have hgap := measureReal_gap_le_cutoff hG M hk hγ hr hR hrR (inv_pos.mpr hq)
  have hrτ : r = γ * τ := by dsimp [τ]; field_simp
  refine (hgap.trans (add_le_add (add_le_add hκupper hnorm) le_rfl)).trans ?_
  change _ ≤ (10000 * Real.exp 1) * (Fintype.card n : ℝ) ^ 5 * √τ * K ^ 2
  conv_lhs => rw [hrτ]
  exact gap_tail_combine hn hK hτ hτ1 hγ hR.le le_rfl hq hq4

/-- **Polynomial eigenvalue-gap tail for a Ginibre perturbation.** For independent standard
complex Gaussian entries, $0<2\gamma\le\|\mathbf{M}\|_2$ and $0<t\le\gamma$, the failure to
admit an eigenvalue listing with all distinct-index gaps exceeding $t$ has probability at most
$10000e n^5\sqrt{t/\gamma}(\|\mathbf{M}\|_2/\gamma+\log(\gamma/t))^2$.
[BanksGarzaVargasSrivastava2025, Lemma B.1], in a weaker polynomial form obtained from the
second-singular-value estimate and eigenvector conditioning. -/
theorem measureReal_not_exists_isEigenvalueListing_le_le_log_sq_of_hasLaw_complexGaussianMatrix
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {G : Ω → Matrix n n ℂ}
    (hG : HasLaw G (complexGaussianMatrix n n) μ) (M : Matrix n n ℂ)
    {γ t : ℝ} (hγ : 0 < γ) (hγM : 2 * γ ≤ specNorm M) (ht : 0 < t) (htγ : t ≤ γ) :
    μ.real {ω | ¬ ∃ d : n → ℂ,
      IsEigenvalueListing (M + (γ / √(Fintype.card n : ℝ)) • G ω) d ∧
        ∀ i j, i ≠ j → t < ‖d i - d j‖} ≤
      (10000 * Real.exp 1) * (Fintype.card n : ℝ) ^ 5 * √(t / γ) *
        (specNorm M / γ + Real.log (γ / t)) ^ 2 := by
  by_cases hn : 2 ≤ Fintype.card n
  · simpa only [inv_div] using measureReal_gap_le_log_sq_of_card_eq_add_two
      hG M (k := Fintype.card n - 2) (by omega) hγ hγM ht htγ
  · have hnle : Fintype.card n ≤ 1 := by omega
    have : Subsingleton n := ⟨Fintype.card_le_one_iff.mp hnle⟩
    have he : {ω | ¬ ∃ d : n → ℂ,
        IsEigenvalueListing (M + (γ / √(Fintype.card n : ℝ)) • G ω) d ∧
          ∀ i j, i ≠ j → t < ‖d i - d j‖} = ∅ := by
      apply Set.eq_empty_of_forall_notMem
      intro ω hω
      obtain ⟨d, hd⟩ := exists_isEigenvalueListing
        (M + (γ / √(Fintype.card n : ℝ)) • G ω)
      exact hω ⟨d, hd, fun i j hij => (hij (Subsingleton.elim i j)).elim⟩
    rw [he, measureReal_empty]
    positivity

/-- **Polynomial eigenvalue-gap tail.** An
$O(n^5(t/\gamma)^{1/2}(\|\mathbf{M}\|_2/\gamma+\log(\gamma/t))^2)$ tail suffices for independent
standard complex Gaussian entries, $0<2\gamma\le\|\mathbf{M}\|_2$ and $0<t\le\gamma$.
The constants are absolute. [BanksGarzaVargasSrivastava2025, Lemma B.1], in a weaker
polynomial form, via a disk net and the conditioning tail. -/
theorem
  exists_forall_measureReal_not_exists_isEigenvalueListing_le_of_hasLaw_complexGaussianMatrix :
    ∃ (C a b c : ℝ), 0 < b ∧ ∀ {Ω : Type} {_mΩ : MeasurableSpace Ω} {μ : Measure Ω}
      {n : Type} [Fintype n] [DecidableEq n] {G : Ω → Matrix n n ℂ},
      HasLaw G (complexGaussianMatrix n n) μ → ∀ (M : Matrix n n ℂ) {γ t : ℝ},
      0 < γ → 2 * γ ≤ specNorm M → 0 < t → t ≤ γ →
      μ.real {ω | ¬ ∃ d : n → ℂ,
        IsEigenvalueListing (M + (γ / √(Fintype.card n : ℝ)) • G ω) d ∧
          ∀ i j, i ≠ j → t < ‖d i - d j‖} ≤
        C * (Fintype.card n : ℝ) ^ a * (t / γ) ^ b *
          (specNorm M / γ + Real.log (γ / t)) ^ c := by
  refine ⟨10000 * Real.exp 1, 5, 1 / 2, 2, by norm_num, ?_⟩
  intro Ω _mΩ μ n _ _ G hG M γ t hγ hγM ht htγ
  simpa only [Real.rpow_ofNat, Real.sqrt_eq_rpow] using
    measureReal_not_exists_isEigenvalueListing_le_le_log_sq_of_hasLaw_complexGaussianMatrix
      hG M hγ hγM ht htγ

end NLAlib
