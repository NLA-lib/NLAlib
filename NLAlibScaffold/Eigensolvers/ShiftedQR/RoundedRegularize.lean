/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlibScaffold.Eigensolvers.ShiftedQR.RoundedExc
public import NLAlibScaffold.Eigensolvers.ShiftedQR.RoundedRitz

/-!
# The rounded `Regularize`

`Regularize` ([BanksGarzaVargasSrivastava2022, §4.2], called $\mathsf{RitzOrDecouple}$ there)
computes forward-approximate Ritz values with `SmallEig`, perturbs each by an independent uniform
sample of a small disk, and tests the perturbed values with `Optimal`. If they are optimal it
returns them; otherwise the dichotomy
(`NLAlib.exists_mem_le_norm_inv_pow_of_not_isOptimalRitzValues`) gives one among them whose degree $k$ step decouples, and the program tries them in turn. The
random perturbation keeps every shift away from the spectrum, which the forward error of the
rounded steps needs.

## Main results

* `NLAlib.ShiftedQR.regularize_bad_window_le`: one perturbation comes within
  $\eta = R\sqrt{\varphi/(2k)}$ of an eigenvalue with probability at most $\varphi/(2k)$.
* `NLAlib.exists_norm_subdiag_le_hessenbergPotential`: some bottom subdiagonal entry is at most
  the potential.
-/

@[expose] public section

open MeasureTheory

namespace NLAlib

variable {n : ℕ}

/-- **Some bottom subdiagonal entry is at most the potential**: for $1 \le k \le n$ one of the
last $k$ subdiagonal entries has $\lvert\mathbf{H}_{i+1,i}\rvert \le \psi_k(\mathbf{H})$, the
geometric mean of their moduli. -/
theorem exists_norm_subdiag_le_hessenbergPotential {k : ℕ} (hk : 0 < k) (hkn : k ≤ n)
    (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    ∃ i : Fin n, n ≤ (i : ℕ) + k ∧ ‖H i.succ i.castSucc‖ ≤ hessenbergPotential k H := by
  set S := Finset.univ.filter (fun i : Fin n => n ≤ (i : ℕ) + k)
  have hmem : (⟨n - k, by omega⟩ : Fin n) ∈ S := by
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  have hne : S.Nonempty := ⟨_, hmem⟩
  obtain ⟨i0, hi0, hmin⟩ := Finset.exists_min_image _ (fun i : Fin n => ‖H i.succ i.castSucc‖) hne
  have hcard : S.card = k := by
    rw [← Finset.card_map Fin.valEmbedding,
      show S.map Fin.valEmbedding = Finset.Ico (n - k) n by
        ext x
        simp only [S, Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
          Fin.valEmbedding_apply, Finset.mem_Ico]
        constructor
        · rintro ⟨i, hi, rfl⟩; exact ⟨by omega, i.isLt⟩
        · intro hx; exact ⟨⟨x, hx.2⟩, by simp only; omega, rfl⟩]
    simp only [Nat.card_Ico]; omega
  refine ⟨i0, (Finset.mem_filter.mp hi0).2, ?_⟩
  have hprod : ‖H i0.succ i0.castSucc‖ ^ k ≤ hessenbergPotential k H ^ k := by
    rw [hessenbergPotential_pow hk]
    calc ‖H i0.succ i0.castSucc‖ ^ k = ∏ _i ∈ S, ‖H i0.succ i0.castSucc‖ := by
          rw [Finset.prod_const, hcard]
      _ ≤ _ := Finset.prod_le_prod (fun _ _ => norm_nonneg _) hmin
  exact le_of_pow_le_pow_left₀ hk.ne' (hessenbergPotential_nonneg k H) hprod

end NLAlib

namespace NLAlib.ShiftedQR

/-- **The bad draws of one random shift regularization** ([BanksGarzaVargasSrivastava2022,
Lemma 3.10], one sample, as `Regularize` uses it): for a centre $c$, complex numbers
$\lambda_1, \dots, \lambda_N$ whose distinct values are at distance at least $4R$, $R > 0$,
$k \ge 1$ and $0 \le \varphi \le 1$, the window $x \in \mathbb{R}^2$ of two uniform draws on
$[0, 1]$ lies off the unit square or makes the polar sample $w$ of radius $R$ bring $c + w$
within $\eta = R\sqrt{\varphi/(2k)}$ of some $\lambda_i$ with probability at most
$\varphi/(2k)$. Over the $k$ draws of `Regularize` this is the paper's $\varphi/2$. -/
theorem regularize_bad_window_le (c : ℂ) {N : ℕ} (e : Fin N → ℂ) {k : ℕ} {R φ : ℝ}
    (hk : 0 < k) (hR : 0 < R) (hφ : 0 ≤ φ) (hφ1 : φ ≤ 1)
    (hsep : ∀ i j, e i ≠ e j → 4 * R ≤ ‖e i - e j‖) :
    (Measure.pi fun _ : Fin 2 => (volume : Measure ℝ).restrict (Set.Icc 0 1)).real
      {x | (∃ j, x j ∉ Set.Icc (0 : ℝ) 1) ∨
        ∃ i, ‖c + polarDisk 0 R x - e i‖ < R * √(φ / (2 * k))} ≤ φ / (2 * k) := by
  classical
  set η := R * √(φ / (2 * k)) with hη_def
  set Λ : Finset ℂ := Finset.univ.image e
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hq0 : 0 ≤ φ / (2 * k) := by positivity
  have hq1 : φ / (2 * k) ≤ 1 := by rw [div_le_iff₀ (by positivity)]; linarith
  have hη0 : 0 ≤ η := by positivity
  have hηR : η ≤ R := mul_le_of_le_one_right hR.le (Real.sqrt_le_one.mpr hq1)
  have hΛ : ∀ a ∈ Λ, ∀ b ∈ Λ, a ≠ b → 2 * (η + R) ≤ ‖a - b‖ := by
    intro a ha b hb hab
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hb
    linarith [hsep i j hab]
  have hD3 := measureReal_exists_norm_add_sub_lt_le (fun _ : Fin 1 => c) Λ hR hη0 hΛ
  set U : Set ℂ := {w | ∃ a ∈ Λ, ‖c + w - a‖ < η}
  have hU : MeasurableSet U := by
    have : U = ⋃ a ∈ Λ, {w | ‖c + w - a‖ < η} := by ext; simp [U]
    rw [this]
    exact Finset.measurableSet_biUnion _ fun a _ => measurableSet_lt (by fun_prop)
      measurable_const
  have h1 : (diskUniform 0 R).real U ≤ (η / R) ^ 2 := by
    have hmp := measurePreserving_funUnique (diskUniform 0 R) (Fin 1)
    rw [← hmp.measureReal_preimage hU.nullMeasurableSet]
    refine le_trans (le_of_eq ?_) (by simpa using hD3)
    congr 1
  set μ := Measure.pi fun _ : Fin 2 => (volume : Measure ℝ).restrict (Set.Icc 0 1)
  set A : Set (Fin 2 → ℝ) := ⋃ j, (fun x : Fin 2 → ℝ => x j) ⁻¹' (Set.Icc (0 : ℝ) 1)ᶜ
  have hmeas : Measurable (polarDisk 0 R) := by unfold polarDisk; fun_prop
  have hset : {x : Fin 2 → ℝ | (∃ j, x j ∉ Set.Icc (0 : ℝ) 1) ∨
      ∃ i, ‖c + polarDisk 0 R x - e i‖ < η} = A ∪ polarDisk 0 R ⁻¹' U := by
    ext x; simp [A, U, Λ]
  have hA0 : μ A = 0 := by
    refine measure_iUnion_null fun j => Measure.pi_eval_preimage_null _ ?_
    rw [Measure.restrict_apply' measurableSet_Icc, Set.compl_inter_self, measure_empty]
  rw [hset]
  calc μ.real (A ∪ polarDisk 0 R ⁻¹' U) ≤ μ.real A + μ.real (polarDisk 0 R ⁻¹' U) :=
        measureReal_union_le _ _
    _ = (diskUniform 0 R).real U := by
        rw [measureReal_def, hA0, ENNReal.toReal_zero, zero_add,
          ← map_measureReal_apply hmeas hU, map_polarDisk_eq_diskUniform 0 hR]
    _ ≤ (η / R) ^ 2 := h1
    _ = φ / (2 * k) := by rw [hη_def, mul_div_cancel_left₀ _ hR.ne', Real.sq_sqrt hq0]

end NLAlib.ShiftedQR
