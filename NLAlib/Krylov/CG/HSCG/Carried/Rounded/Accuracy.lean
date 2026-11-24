/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.CG.HSCG.Carried.Rounded.ScalarTheorem
public import NLAlib.Krylov.FinitePrecision.CGErrorTracking
public import NLAlib.Krylov.FinitePrecision.CGSpectralConvergence

/-!
# Attainable accuracy and error tracking of the actual rounded CG output

The rounded program returns an existing `NLAlib.CGRun` tied to its stored output. This file
transfers to that run the residual gap, the relative tracking of energy decrements, the
inverse-tridiagonal estimate and convergence on a set containing the spectrum of the backward
model. It adds no numerical argument except the case split on how the program stopped, which
gives the attainable accuracy of the true residual of the stored iterate.

## Main results

* `NLAlib.Krylov.CG.HSCG.Carried.Rounded.RunAccuracy`: the transferred guarantees of a run.
* `NLAlib.Krylov.CG.HSCG.Carried.Rounded.runAccuracy_of_run`: every run in the window has them.
* `NLAlib.Krylov.CG.HSCG.Carried.Rounded.StableOutput.accurate`: they hold for the actual output.
* `NLAlib.Krylov.CG.HSCG.Carried.Rounded.StableOutput.exists_norm_sub_mulVec_le`: the true
  residual of the stored iterate, however the program stopped.
* `NLAlib.Krylov.CG.HSCG.Carried.Rounded.Stored.Certification.exec_scalarProgram_norm_sub_mulVec_le`
  (the same bound for the scalar program).
-/

@[expose] public section

namespace NLAlib.Krylov.CG.HSCG.Carried.Rounded

open Ops
open scoped Matrix

/-- The residual gap, relative decrement tracking, inverse-tridiagonal estimate and convergence
on any compact set containing the eigenvalue intervals of the backward model, for a run. -/
def RunAccuracy {n m : ℕ} (R : CGRun n m) (a a' : ℝ) : Prop :=
  ∀ xs : Fin n → ℝ, R.A *ᵥ xs = R.b →
    ‖WithLp.toLp 2 (R.b - R.A *ᵥ R.x m - R.r m)‖ ≤
      11 * m * R.ε * a' * (‖WithLp.toLp 2 xs‖ + Real.sqrt (quadForm R.A xs) / Real.sqrt a) ∧
    (∀ j d, j + d ≤ m →
      |quadForm R.A (xs - R.x j) - quadForm R.A (xs - R.x (j + d)) -
          ∑ i ∈ Finset.Ico j (j + d), R.γ i * R.ρ i ^ 2| ≤
        cgEnergyTrackingRelativeFactor m * R.ε * (a' / a) *
            ∑ i ∈ Finset.Ico j (j + d), R.γ i * R.ρ i ^ 2 +
          cgEnergyTrackingUpdateFactor (j + d) * d * R.ε * (a' / a) *
            (‖WithLp.toLp 2 R.b‖ ^ 2 / a)) ∧
    (∀ j, j + 1 ≤ m →
      |quadForm R.A (xs - R.x (j + 1)) -
          (quadForm R.A xs - ‖WithLp.toLp 2 R.b‖ ^ 2 * (cgTridiagonal R.γ R.ρ (j + 1))⁻¹ 0 0)| ≤
        cgEnergyEstimatorFactor 0 (j + 1) * R.ε * (a' / a) * (‖WithLp.toLp 2 R.b‖ ^ 2 / a)) ∧
    ∀ S : Set ℝ, IsCompact S →
      (⋃ i ∈ Set.Iio n, Set.Icc
        (eigenvalue R.A i - cgBackwardFactor m * R.ε * (a' / a) * a')
        (eigenvalue R.A i + cgBackwardFactor m * R.ε * (a' / a) * a')) ⊆ S →
      ∀ j ≤ m, quadForm R.A (xs - R.x j) ≤
        residualMinimax S j ^ 2 * (quadForm R.A xs +
          2 * ‖WithLp.toLp 2 R.b‖ ^ 2 * (cgBackwardFactor m * R.ε * (a' / a) * a') / a ^ 2) +
        2 * ‖WithLp.toLp 2 R.b‖ ^ 2 * (cgBackwardFactor m * R.ε * (a' / a) * a') / a ^ 2 +
        cgEnergyFactor j * R.ε * (a' / a) * (‖WithLp.toLp 2 R.b‖ ^ 2 / a)

/-- Every run in the precision window has the transferred guarantees. -/
theorem runAccuracy_of_run {n m : ℕ} (R : CGRun n m) {a a' : ℝ} (ha : 0 < a)
    (hs : spectrum ℝ R.A ⊆ Set.Icc a a')
    (hsmall : (m : ℝ) ^ 2 * Real.sqrt m * R.ε * (a' / a) ^ 2 ≤ 1 / 10 ^ 5) :
    RunAccuracy R a a' := fun _ hx =>
  ⟨R.norm_sub_mulVec_x_sub_r_le_energy ha hs hsmall hx,
    fun _ _ hjd => R.abs_quadForm_sub_x_sub_quadForm_sub_x_add_sub_sum_le ha hs hsmall hx hjd,
    fun _ hj => R.abs_quadForm_sub_x_succ_sub_sub_inv_cgTridiagonal_le ha hs hsmall hx hj,
    fun _ hS hU _ hj => R.quadForm_sub_x_le_residualMinimax_sq_mul_add ha hs hsmall
      (R.frobNorm_backwardH_sub_dilatedH_le ha hs hsmall) hS hU hx hj⟩

section Output

variable {K : Type} [Inhabited K] {n cap : ℕ} {dec : K → ℝ}
  {A : Matrix (Fin n) (Fin n) ℝ} {rhs : Fin n → ℝ} {e a a' : ℝ}
  {x r p v : ℕ × ℕ} {μ : Mem K}

/-- The window at the cap gives the window at the rounds performed. -/
theorem window_of_le {m : ℕ} (hm : m ≤ cap) (he : 0 ≤ e)
    (hwindow : (cap : ℝ) ^ 2 * Real.sqrt cap * e * (a' / a) ^ 2 ≤ 1 / 10 ^ 5) :
    (m : ℝ) ^ 2 * Real.sqrt m * e * (a' / a) ^ 2 ≤ 1 / 10 ^ 5 := by
  refine le_trans ?_ hwindow
  gcongr

/-- The actual output: the zero-step alternative, or the same run with the transferred
guarantees. -/
theorem StableOutput.accurate (h : StableOutput dec A rhs e a a' cap x r p v μ) (ha : 0 < a)
    (hs : spectrum ℝ A ⊆ Set.Icc a a')
    (hwindow : (cap : ℝ) ^ 2 * Real.sqrt cap * e * (a' / a) ^ 2 ≤ 1 / 10 ^ 5) :
    ((cap = 0 ∨ rhs = 0) ∧ ∃ rho, StoresValues dec n x r p v ⟨0, rhs, rhs⟩ rho μ) ∨
      ∃ m : ℕ, ∃ R : CGRun n m, m ≤ cap ∧ R.A = A ∧ R.b = rhs ∧ R.ε = e ∧
        StoresValues dec n x r p v ⟨R.x m, R.r m, R.p m⟩ (R.ν m) μ ∧
        (m < cap → R.r m = 0) ∧ RunAccuracy R a a' := by
  rcases h with hz | ⟨m, R, hm, hA, hb, he, hst, hstop, -⟩
  · exact Or.inl hz
  · refine Or.inr ⟨m, R, hm, hA, hb, he, hst, hstop, runAccuracy_of_run R ha (by rwa [hA]) ?_⟩
    rw [he]
    exact window_of_le hm (he ▸ R.ε_nonneg) hwindow

/-- Attainable accuracy of the stored CG iterate. If the cap is at least
$k_\star(\kappa, E, 1)$, the true residual of the stored iterate satisfies
$$\|\mathbf{b} - \mathbf{A}\hat{\mathbf{x}}\| \le (11k + 8)\,E\,a'\,
(\|\mathbf{x}_\star\| + \|\mathbf{x}_\star\|_{\mathbf{A}}/\sqrt{a})$$
for every solution, both when the program reaches the cap and when it stops early on a zero
computed residual, where the bound is the residual gap. -/
theorem StableOutput.exists_norm_sub_mulVec_le (h : StableOutput dec A rhs e a a' cap x r p v μ)
    (ha : 0 < a) (haa : a ≤ a') (hs : spectrum ℝ A ⊆ Set.Icc a a') (he : 0 < e) (hcap : 0 < cap)
    (hk : cgKStar (a' / a) e 1 ≤ cap)
    (hwindow : (cap : ℝ) ^ 2 * Real.sqrt cap * e * (a' / a) ^ 2 ≤ 1 / 10 ^ 5) :
    ∃ (s : CGState ℝ (Fin n)) (rho : ℝ), StoresValues dec n x r p v s rho μ ∧
      ∀ xs : Fin n → ℝ, A *ᵥ xs = rhs →
        ‖WithLp.toLp 2 (rhs - A *ᵥ s.x)‖ ≤
          (11 * cap + 8) * e * a' *
            (‖WithLp.toLp 2 xs‖ + Real.sqrt (quadForm A xs) / Real.sqrt a) := by
  have ha' : 0 < a' := ha.trans_le haa
  rcases h with ⟨hz, rho, hst⟩ | ⟨m, R, hm, rfl, rfl, rfl, hst, hstop, -⟩
  · refine ⟨⟨0, rhs, rhs⟩, rho, hst, fun xs _ => ?_⟩
    obtain rfl : rhs = 0 := hz.resolve_left hcap.ne'
    change ‖WithLp.toLp 2 ((0 : Fin n → ℝ) - A *ᵥ (0 : Fin n → ℝ))‖ ≤ _
    simp only [Matrix.mulVec_zero, sub_zero, WithLp.toLp_zero, norm_zero]
    positivity
  · refine ⟨⟨R.x m, R.r m, R.p m⟩, R.ν m, hst, fun xs hxs => ?_⟩
    change ‖WithLp.toLp 2 (R.b - R.A *ᵥ R.x m)‖ ≤ _
    have hsmall := window_of_le hm he.le hwindow
    rcases hm.lt_or_eq with hlt | rfl
    · have hgap := R.norm_sub_mulVec_x_sub_r_le_energy ha hs hsmall hxs
      rw [hstop hlt, sub_zero] at hgap
      refine hgap.trans ?_
      have hmc : (m : ℝ) ≤ cap := Nat.cast_le.mpr hm
      gcongr
      linarith
    · exact R.norm_sub_mulVec_x_le_of_cgKStar_le ha hs hsmall he hxs hk

end Output

namespace Stored.Certification

variable {lower upper : (Fin 2 → ℕ) → ℝ}
variable {domain : (Fin 2 → ℕ) → Prop} {admitted : ∃ d, domain d}
  {supply : ∀ d, domain d →
    ∃ x : Matrix (Fin (d 0)) (Fin (d 0)) ℝ × (Fin (d 0) → ℝ), accepts lower upper d x}

/-- **Scalar conjugate gradient in rounded arithmetic: attainable accuracy.** Let
$\mathbf{A} \in \mathbb{R}^{n \times n}$ be symmetric with spectrum in $[a, a']$, $0 < a \le a'$,
stored entry by entry, let $\mathbf{b} \in \mathbb{R}^n$, and write $\kappa = a'/a$. Run the
scalar carried conjugate gradient program from zero on a machine in the standard model with unit
roundoff $u$, with an allowance $0 < E \le 1/100$ dominating the rounding of its scalar, vector
and matrix-vector operations, $3 E a' \le a$, a cap $k > 0$ with
$k \ge k_\star(\kappa, E, 1)$ and $k^{2} \sqrt{k}\, E\, \kappa^{2} \le 10^{-5}$. Then every run
succeeds within $33 n^{2} k + 157 n k + 242 k + 50 n + 127$ instructions, and the iterate
$\hat{\mathbf{x}}$ it stores satisfies, for every solution $\mathbf{x}_\star$,
$$\|\mathbf{b} - \mathbf{A}\hat{\mathbf{x}}\| \le (11k + 8) E a'
(\|\mathbf{x}_\star\| + \|\mathbf{x}_\star\|_{\mathbf{A}}/\sqrt{a}).$$
The hypotheses on $k$ and $E$ together restrict $\kappa$ to small values.
[Greenbaum1997SIMAX]; [StrakosTichy2002, (7.16)], for the run the program executes. -/
theorem exec_scalarProgram_norm_sub_mulVec_le (M : Machine ℝ) (u : ℝ)
    (hM : StdModel u id M) (hu : 0 ≤ u) (em E : (Fin 2 → ℕ) → ℝ)
    (hMatvec : ∀ d, domain d → ScalarProducts.roundoff u (d 0) * Real.sqrt (d 0) ≤ em d)
    (hAccuracy : ∀ d, domain d → Standard.Accuracy (em d) u (E d) (Blas.seq.err u) (d 0))
    (ha : ∀ d, domain d → 0 < lower d)
    (hprec : ∀ d, domain d → 3 * E d * upper d ≤ lower d)
    (hwindow : ∀ d, domain d → (d 1 : ℝ) ^ 2 * Real.sqrt (d 1) * E d *
      (upper d / lower d) ^ 2 ≤ 1 / 10 ^ 5)
    {d : Fin 2 → ℕ} (hd : domain d) (haa : lower d ≤ upper d) (hE : 0 < E d) (hcap : 0 < d 1)
    (hk : cgKStar (upper d / lower d) (E d) 1 ≤ d 1)
    (x : (problem lower upper domain admitted supply).Input d)
    (I : Interp ScalarOp CmpTst ℝ)
    (hI : (RoundedScalarBlas.model (problem lower upper domain admitted supply) M).contracts
      d x I) (τ : Tape ℝ) :
    ∃ st, Reference.Execution scalarProgram I RoundedScalarBlas.resources
        (problem lower upper domain admitted supply).formats τ d
        ((problem lower upper domain admitted supply).initial d x) st ∧
      RoundedScalarBlas.resources.work st.cost ≤
        33 * d 0 ^ 2 * d 1 + 157 * d 0 * d 1 + 242 * d 1 + 50 * d 0 + 127 ∧
      ∃ (s : CGState ℝ (Fin (d 0))) (rho : ℝ),
        StoresValues id (d 0) (2, 0) (3, 0) (4, 0) (5, 0) s rho st.mem ∧
        ∀ xs : Fin (d 0) → ℝ, inputMatrix x *ᵥ xs = inputRhs x →
          ‖WithLp.toLp 2 (inputRhs x - inputMatrix x *ᵥ s.x)‖ ≤
            (11 * (d 1 : ℝ) + 8) * E d * upper d *
              (‖WithLp.toLp 2 xs‖ +
                Real.sqrt (quadForm (inputMatrix x) xs) / Real.sqrt (lower d)) := by
  obtain ⟨st, hr, -, -, hw, -, -, hg⟩ := (scalarCountedAlgorithm lower upper domain admitted
    supply M u hM hu em E hMatvec hAccuracy ha hprec hwindow).correct d hd x I hI τ
  have hout : StableOutput id (inputMatrix x) (inputRhs x) (E d) (lower d) (upper d) (d 1)
      (2, 0) (3, 0) (4, 0) (5, 0) st.mem := hg.2
  exact ⟨st, hr, hw, hout.exists_norm_sub_mulVec_le (ha d hd) haa x.property.1.2 hE hcap hk
    (hwindow d hd)⟩

end Stored.Certification

end NLAlib.Krylov.CG.HSCG.Carried.Rounded
