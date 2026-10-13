/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Majorization.KyFan
public import NLAlib.Matrix.Spectral.SingularValueInequalities

/-!
# Lidskii's inequalities

For Hermitian `A` and `B`, the vector of eigenvalue differences `λ_i(A + B) - λ_i(A)` is
majorized by the eigenvalues of `B`. For arbitrary matrices, the absolute differences of
singular values `|σ_i(A + E) - σ_i(A)|` are weakly majorized by the singular values of `E`. The
second statement is the general form of Mirsky's theorem: with Fan dominance it gives the
`1`-Lipschitz property of singular values in every unitarily invariant norm.

## Main results

* `NLAlib.sum_eigenvalue_add_sub_le_sum_range`, `NLAlib.majorized_eigenvalue_add_sub`: Lidskii.
* `NLAlib.sum_abs_singularValues_add_sub_le_kyFanNorm`,
  `NLAlib.weaklyMajorized_abs_singularValues_add_sub`: the singular value form.
-/

@[expose] public section

open scoped Matrix ComplexOrder MatrixOrder

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {m n : Type*} [Fintype m] [Fintype n]

/-! ### Eigenvalues -/

/-- The positive part of `B - c • 1`: a positive semidefinite `P` with `B ≤ P + c • 1` whose trace
is the sum of the positive parts of the `λ_i(B) - c`. -/
private theorem exists_posSemidef_le_add_smul_one [DecidableEq n] {B : Matrix n n 𝕜}
    (hB : B.IsHermitian) (c : ℝ) :
    ∃ P : Matrix n n 𝕜, P.PosSemidef ∧ B ≤ P + c • (1 : Matrix n n 𝕜) ∧
      RCLike.re P.trace = ∑ i ∈ Finset.range (Fintype.card n), max (eigenvalue B i - c) 0 := by
  obtain ⟨U, hU, hBU⟩ := hB.exists_eq_mul_diagonal_mul_conjTranspose
  set d : Fin (Fintype.card n) → ℝ := fun i => eigenvalue B i
  replace hBU : B = U * Matrix.diagonal (fun i => ((d i : ℝ) : 𝕜)) * Uᴴ := hBU
  have hUU : U * Uᴴ = 1 := hU.mul_conjTranspose_self_of_card_eq (Fintype.card_fin _).symm
  refine ⟨U * Matrix.diagonal (fun i => ((max (d i - c) 0 : ℝ) : 𝕜)) * Uᴴ, ?_, ?_, ?_⟩
  · exact (Matrix.posSemidef_diagonal_iff.mpr fun i =>
      RCLike.ofReal_nonneg.mpr (le_max_right _ _)).mul_mul_conjTranspose_same U
  · have hsub : U * Matrix.diagonal (fun i => ((max (d i - c) 0 : ℝ) : 𝕜)) * Uᴴ +
        c • (1 : Matrix n n 𝕜) - B =
        U * Matrix.diagonal (fun i => ((max (d i - c) 0 + c - d i : ℝ) : 𝕜)) * Uᴴ := by
      have hD : Matrix.diagonal (fun i => ((max (d i - c) 0 + c - d i : ℝ) : 𝕜)) =
          Matrix.diagonal (fun i => ((max (d i - c) 0 : ℝ) : 𝕜)) + c • (1 : Matrix _ _ 𝕜) -
            Matrix.diagonal (fun i => ((d i : ℝ) : 𝕜)) := by
        rw [← Matrix.diagonal_one, ← Matrix.diagonal_smul, Matrix.diagonal_add,
          Matrix.diagonal_sub]
        congr 1
        funext i
        simp only [Pi.smul_apply, RCLike.real_smul_eq_coe_mul, mul_one, RCLike.ofReal_add,
          RCLike.ofReal_sub]
      rw [hD, hBU]
      simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul,
        Matrix.smul_mul, Matrix.mul_one, hUU]
    rw [Matrix.le_iff, hsub]
    refine (Matrix.posSemidef_diagonal_iff.mpr fun i =>
      RCLike.ofReal_nonneg.mpr ?_).mul_mul_conjTranspose_same U
    linarith [le_max_left (d i - c) 0]
  · rw [Matrix.trace_mul_cycle, hU.conjTranspose_mul_self, Matrix.one_mul, Matrix.trace_diagonal,
      ← RCLike.ofReal_sum, RCLike.ofReal_re]
    exact Fin.sum_univ_eq_sum_range (fun i => max (eigenvalue B i - c) 0) _

/-- **Lidskii's inequality**, sum form. For Hermitian `A`, `B` and any set `J` of valid indices,
`∑ j ∈ J, (λ_j(A + B) - λ_j(A)) ≤ ∑ i < |J|, λ_i(B)`.
[HornJohnson2013, Theorem 4.3.47(b)]; [Bhatia1997, Theorem III.4.1].
Port of `NLAlib.sum_eigenvalues₀_add_le_sum_add_eigenvaluePrefix`, there over `ℝ`; the proof here
is new.
Result: lidskii-inequality -/
theorem sum_eigenvalue_add_sub_le_sum_range {A B : Matrix n n 𝕜} (hA : A.IsHermitian)
    (hB : B.IsHermitian) {J : Finset ℕ} (hJ : ∀ j ∈ J, j < Fintype.card n) :
    ∑ j ∈ J, (eigenvalue (A + B) j - eigenvalue A j) ≤
      ∑ i ∈ Finset.range J.card, eigenvalue B i := by
  classical
  rcases J.eq_empty_or_nonempty with rfl | hne
  · simp
  have hsub : J ⊆ Finset.range (Fintype.card n) := fun j hj => Finset.mem_range.mpr (hJ j hj)
  have hk0 : 0 < J.card := Finset.card_pos.mpr hne
  have hkN : J.card ≤ Fintype.card n := by simpa using Finset.card_le_card hsub
  obtain ⟨P, hP, hBP, htr⟩ := exists_posSemidef_le_add_smul_one hB (eigenvalue B (J.card - 1))
  set c := eigenvalue B (J.card - 1)
  have hAP : (A + P).IsHermitian := hA.add hP.isHermitian
  have h1 : ∀ j < Fintype.card n, eigenvalue (A + B) j ≤ eigenvalue (A + P) j + c := by
    intro j hj
    rw [← hAP.eigenvalue_add_smul_one c hj, add_assoc]
    exact eigenvalue_le_eigenvalue_of_le (add_le_add_right hBP A) (hA.add hB) j
  have h2 : ∀ j, 0 ≤ eigenvalue (A + P) j - eigenvalue A j := fun j =>
    sub_nonneg.mpr (eigenvalue_le_eigenvalue_add_of_posSemidef hA hP j)
  have h3 : ∑ i ∈ Finset.range (Fintype.card n), max (eigenvalue B i - c) 0 =
      ∑ i ∈ Finset.range J.card, eigenvalue B i - J.card * c := by
    rw [← Finset.sum_range_add_sum_Ico _ hkN, Finset.sum_eq_zero (s := Finset.Ico _ _), add_zero]
    · rw [eq_sub_iff_add_eq, ← nsmul_eq_mul, ← Finset.card_range J.card, ← Finset.sum_const,
        Finset.card_range, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [max_eq_left (sub_nonneg.mpr ?_), sub_add_cancel]
      have hi' := Finset.mem_range.mp hi
      exact hB.eigenvalue_le_eigenvalue (by omega) (by omega)
    · intro i hi
      have hi' := Finset.mem_Ico.mp hi
      exact max_eq_right (sub_nonpos.mpr (hB.eigenvalue_le_eigenvalue (by omega) hi'.2))
  calc ∑ j ∈ J, (eigenvalue (A + B) j - eigenvalue A j)
      ≤ ∑ j ∈ J, ((eigenvalue (A + P) j - eigenvalue A j) + c) :=
        Finset.sum_le_sum fun j hj => by linarith [h1 j (hJ j hj)]
    _ = ∑ j ∈ J, (eigenvalue (A + P) j - eigenvalue A j) + J.card * c := by
        rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ j ∈ Finset.range (Fintype.card n), (eigenvalue (A + P) j - eigenvalue A j) +
          J.card * c :=
        add_le_add_left (Finset.sum_le_sum_of_subset_of_nonneg hsub fun j _ _ => h2 j) _
    _ = ∑ i ∈ Finset.range J.card, eigenvalue B i := by
        rw [Finset.sum_sub_distrib, ← hAP.re_trace_eq_sum_range_eigenvalue,
          ← hA.re_trace_eq_sum_range_eigenvalue, Matrix.trace_add, map_add, add_sub_cancel_left,
          htr, h3, sub_add_cancel]

/-- **Lidskii's inequality**, majorization form. For Hermitian `A`, `B`, the eigenvalue
differences `λ_i(A + B) - λ_i(A)` are majorized by the eigenvalues of `B`.
[Bhatia1997, Corollary III.4.2].
Port of `NLAlib.majorized_eigenvalues₀_add_sub`, there over `ℝ`.
Result: lidskii-inequality -/
theorem majorized_eigenvalue_add_sub {A B : Matrix n n 𝕜} (hA : A.IsHermitian)
    (hB : B.IsHermitian) :
    Majorized (fun i : Fin (Fintype.card n) => eigenvalue (A + B) i - eigenvalue A i)
      (fun i : Fin (Fintype.card n) => eigenvalue B i) := by
  refine ⟨weaklyMajorized_fin_of_forall_sum_le (f := eigenvalue B)
    (fun i _ j hj hij => hB.eigenvalue_le_eigenvalue hij hj) fun S => ?_, ?_⟩
  · have h := sum_eigenvalue_add_sub_le_sum_range hA hB (J := S.map Fin.valEmbedding)
      fun j hj => by
        obtain ⟨i, -, rfl⟩ := Finset.mem_map.mp hj
        exact i.isLt
    rwa [Finset.sum_map, Finset.card_map] at h
  · rw [Fin.sum_univ_eq_sum_range (fun i => eigenvalue (A + B) i - eigenvalue A i),
      Fin.sum_univ_eq_sum_range (fun i => eigenvalue B i), Finset.sum_sub_distrib,
      ← (hA.add hB).re_trace_eq_sum_range_eigenvalue, ← hA.re_trace_eq_sum_range_eigenvalue,
      ← hB.re_trace_eq_sum_range_eigenvalue, Matrix.trace_add, map_add, add_sub_cancel_left]

/-! ### Singular values -/

/-- Lidskii's inequality for singular values, for indices below both dimensions: index `i` of the
dilation is used where the singular value increases, and the mirror index where it decreases. -/
private theorem sum_abs_singularValues_add_sub_le_kyFanNorm_of_lt (A E : Matrix m n 𝕜)
    {T : Finset ℕ} (hT : ∀ i ∈ T, i < min (Fintype.card m) (Fintype.card n)) :
    ∑ i ∈ T, |singularValues (A + E) i - singularValues A i| ≤ kyFanNorm T.card E := by
  classical
  let f : ℕ → ℕ := fun i =>
    if 0 ≤ singularValues (A + E) i - singularValues A i then i
    else Fintype.card m + Fintype.card n - 1 - i
  have hf : Set.InjOn f T := by
    intro i hi j hj hij
    have hi' := hT i hi
    have hj' := hT j hj
    simp only [f] at hij
    split_ifs at hij <;> omega
  have hval (C : Matrix m n 𝕜) {i : ℕ} (hi : i ∈ T) :
      eigenvalue (dilation C) (f i) =
        if 0 ≤ singularValues (A + E) i - singularValues A i then singularValues C i
        else -singularValues C i := by
    have hi' := hT i hi
    have himax : i < max (Fintype.card m) (Fintype.card n) := by omega
    simp only [f]
    split_ifs
    · exact eigenvalue_dilation C himax
    · exact eigenvalue_dilation_of_add_add_one_eq C himax (by omega)
  have hJ : ∀ j ∈ T.image f, j < Fintype.card (m ⊕ n) := by
    intro j hj
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
    have hi' := hT i hi
    rw [Fintype.card_sum]
    simp only [f]
    split_ifs <;> omega
  have key := sum_eigenvalue_add_sub_le_sum_range (isHermitian_dilation A)
    (isHermitian_dilation E) hJ
  rw [Finset.sum_image hf, Finset.card_image_of_injOn hf, ← dilation_add] at key
  have hcard : T.card ≤ min (Fintype.card m) (Fintype.card n) := by
    simpa using Finset.card_le_card fun i hi => Finset.mem_range.mpr (hT i hi)
  calc ∑ i ∈ T, |singularValues (A + E) i - singularValues A i|
      = ∑ i ∈ T, (eigenvalue (dilation (A + E)) (f i) - eigenvalue (dilation A) (f i)) :=
        Finset.sum_congr rfl fun i hi => by
          rw [hval _ hi, hval _ hi]
          split_ifs with h
          · exact abs_of_nonneg h
          · rw [abs_of_neg (not_le.mp h)]
            ring
    _ ≤ ∑ i ∈ Finset.range T.card, eigenvalue (dilation E) i := key
    _ = kyFanNorm T.card E :=
        Finset.sum_congr rfl fun i hi =>
          eigenvalue_dilation E (by have := Finset.mem_range.mp hi; omega)

/-- **Lidskii's inequality for singular values.** For any set `S` of indices,
`∑ i ∈ S, |σ_i(A + E) - σ_i(A)| ≤ ∑ j < |S|, σ_j(E)`.
[HornJohnson1991, Theorem 3.4.5]; [Bhatia1997, Theorem IV.3.4].
Port of `NLAlib.sum_abs_singularValues_add_sub_le_sum_range`, there over `ℝ`.
Result: lidskii-singular-values, mirsky-inequality -/
theorem sum_abs_singularValues_add_sub_le_kyFanNorm (A E : Matrix m n 𝕜) (S : Finset ℕ) :
    ∑ i ∈ S, |singularValues (A + E) i - singularValues A i| ≤ kyFanNorm S.card E := by
  classical
  have hfilter : ∑ i ∈ S, |singularValues (A + E) i - singularValues A i| =
      ∑ i ∈ S with i < min (Fintype.card m) (Fintype.card n),
        |singularValues (A + E) i - singularValues A i| := by
    refine (Finset.sum_filter_of_ne fun i _ hi => ?_).symm
    by_contra hlt
    rcases min_le_iff.mp (not_lt.mp hlt) with h | h
    · rw [singularValues_of_card_rows_le _ h, singularValues_of_card_rows_le _ h] at hi
      simp at hi
    · rw [singularValues_of_card_cols_le _ h, singularValues_of_card_cols_le _ h] at hi
      simp at hi
  rw [hfilter]
  exact (sum_abs_singularValues_add_sub_le_kyFanNorm_of_lt A E fun i hi =>
    (Finset.mem_filter.mp hi).2).trans
      (kyFanNorm_mono_left E (Finset.card_le_card (Finset.filter_subset _ S)))

/-- The absolute differences of the first `N` singular values are weakly majorized by the first
`N` singular values of the perturbation, for every `N`.
[Bhatia1997, Theorem IV.3.4].
Port of `NLAlib.weaklyMajorized_abs_singularValues_add_sub_padded`, there over `ℝ`.
Result: lidskii-singular-values -/
theorem weaklyMajorized_abs_singularValues_add_sub (A E : Matrix m n 𝕜) (N : ℕ) :
    WeaklyMajorized (fun i : Fin N => |singularValues (A + E) i - singularValues A i|)
      (fun i : Fin N => singularValues E i) := by
  refine weaklyMajorized_fin_of_forall_sum_le (f := singularValues E)
    ((singularValues_antitone E).antitoneOn _) fun S => ?_
  have h := sum_abs_singularValues_add_sub_le_kyFanNorm A E (S.map Fin.valEmbedding)
  rwa [Finset.sum_map, Finset.card_map] at h

end NLAlib
