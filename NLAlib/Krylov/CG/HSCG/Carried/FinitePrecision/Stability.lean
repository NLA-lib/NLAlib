/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.CG.HSCG.Carried.FinitePrecision.Linked
public import NLAlib.Krylov.FinitePrecision.CGEnergyEstimator

/-!
# Backward models and physical stability of the actual rounded CG output

The full program's extracted existing run immediately supports the old pure backward-model,
physical-energy and delayed-estimator results. These are properties of the same witness tied
to the actual output vectors and cache. All execution assumptions remain mathematical inputs.

## Main results

* `NLAlib.Krylov.CG.HSCG.Carried.Rounded.Stability` states the transferred numerical guarantees.
* `NLAlib.Krylov.CG.HSCG.Carried.Rounded.runs_solve_seq_stability` gives full program success.
-/

@[expose] public section

namespace NLAlib.Krylov.CG.HSCG.Carried.Rounded

open Ops
open scoped Matrix

/-- The existing run's backward model reproduces computed scalars and residual norms, and its
physical iterates satisfy energy convergence and delayed energy estimation bounds.
[Greenbaum1997SIMAX]; [StrakosTichy2002, §10]. -/
def Stability {n m : ℕ} (R : CGRun n m) (a a' : ℝ) : Prop :=
  R.backwardH.PosDef ∧ spectrum ℝ R.backwardH ⊆ Set.Icc (a / 2) (a' + a / 2) ∧
    frobNorm (R.backwardH - R.dilatedH) ≤ cgBackwardFactor m * R.ε * (a' / a) * a' ∧
    (∀ j < m, cgAlpha R.backwardH (cgState R.backwardH R.dilatedRhs 0 j) = R.γ j) ∧
    (∀ j ≤ m, ‖WithLp.toLp 2 (cgState R.backwardH R.dilatedRhs 0 j).r‖ = R.ρ j) ∧
    (∀ xs : Fin n → ℝ, R.A *ᵥ xs = R.b → ∀ j ≤ m,
      quadForm R.A (xs - R.x j) ≤
        4 * ((Real.sqrt (2 * (a' / a) + 1) - 1) /
          (Real.sqrt (2 * (a' / a) + 1) + 1)) ^ (2 * j) * quadForm R.A xs +
        2 * ‖WithLp.toLp 2 R.b‖ ^ 2 * (cgBackwardFactor m * R.ε * (a' / a) * a') / a ^ 2 +
        cgEnergyFactor j * R.ε * (a' / a) * (‖WithLp.toLp 2 R.b‖ ^ 2 / a)) ∧
    (∀ xs : Fin n → ℝ, R.A *ᵥ xs = R.b → ∀ j d, j + d ≤ m →
      |(quadForm R.A (xs - R.x j) - quadForm R.A (xs - R.x (j + d))) -
        ∑ i ∈ Finset.Ico j (j + d), R.γ i * R.ρ i ^ 2| ≤
      cgEnergyEstimatorFactor j d * R.ε * (a' / a) *
        (‖WithLp.toLp 2 R.b‖ ^ 2 / a))

/-- The existing pure run theorems provide every stability clause directly from the spectral
precision window. No new convergence argument is used in the program transfer. -/
theorem stability_of_run {n m : ℕ} (R : CGRun n m) {a a' : ℝ} (ha : 0 < a)
    (hs : spectrum ℝ R.A ⊆ Set.Icc a a')
    (hsmall : (m : ℝ) ^ 2 * Real.sqrt m * R.ε * (a' / a) ^ 2 ≤ 1 / 10 ^ 5) :
    Stability R a a' := by
  have hspec := R.spectrum_backwardH_subset_Icc ha hs hsmall
  have hpd : R.backwardH.PosDef := R.isHermitian_backwardH.posDef_iff_eigenvalue_pos.mpr
    fun i hi => (show 0 < a / 2 by positivity).trans_le
      (R.isHermitian_backwardH.spectrum_subset_iff.mp hspec i hi).1
  refine ⟨hpd,
    hspec, R.frobNorm_backwardH_sub_dilatedH_le ha hs hsmall,
    fun j hj => R.cgAlpha_backwardH ha hs hsmall hj,
    fun j hj => R.norm_cgState_backwardH_r ha hs hsmall hj,
    fun xs hxs j hj => R.quadForm_sub_x_le_four_mul_pow_add ha hs hsmall hxs hj,
    fun xs hxs j d hjd => R.abs_quadForm_sub_x_sub_quadForm_sub_x_sub_sum_le
      ha hs hsmall hxs hjd⟩

/-- The strengthened actual output retains the zero-step alternative and otherwise exhibits
the same existing run, physical output/cache ties and numerical stability guarantees. -/
def StableOutput {K : Type} [Inhabited K] {n : ℕ} (dec : K → ℝ)
    (A : Matrix (Fin n) (Fin n) ℝ) (rhs : Fin n → ℝ) (e a a' : ℝ) (cap : ℕ)
    (x r p v : ℕ × ℕ) (μ : Mem K) : Prop :=
  ((cap = 0 ∨ rhs = 0) ∧ ∃ rho, StoresValues dec n x r p v ⟨0, rhs, rhs⟩ rho μ) ∨
  ∃ m : ℕ, ∃ R : CGRun n m, m ≤ cap ∧ R.A = A ∧ R.b = rhs ∧ R.ε = e ∧
    StoresValues dec n x r p v ⟨R.x m, R.r m, R.p m⟩ (R.ν m) μ ∧
    (m < cap → R.r m = 0) ∧ Stability R a a'

/-- The program's actual extracted run inherits stability at every possible stopping point
below the input cap. The scalar precision window decreases with the prefix length. -/
theorem Output.stable {K : Type} [Inhabited K] {n cap : ℕ} {dec : K → ℝ}
    {A : Matrix (Fin n) (Fin n) ℝ} {rhs : Fin n → ℝ} {e a a' : ℝ}
    {x r p v : ℕ × ℕ} {μ : Mem K} (h : Output dec A rhs e cap x r p v μ)
    (ha : 0 < a) (hs : spectrum ℝ A ⊆ Set.Icc a a')
    (hwindow : (cap : ℝ) ^ 2 * Real.sqrt cap * e * (a' / a) ^ 2 ≤ 1 / 10 ^ 5) :
    StableOutput dec A rhs e a a' cap x r p v μ := by
  rcases h with hz | ⟨m, R, hm, hA, hb, he, hstored, hstop, _⟩
  · exact Or.inl hz
  · refine Or.inr ⟨m, R, hm, hA, hb, he, hstored, hstop, ?_⟩
    have he0 := R.ε_nonneg
    have hsmall : (m : ℝ) ^ 2 * Real.sqrt m * R.ε * (a' / a) ^ 2 ≤ 1 / 10 ^ 5 := by
      calc
        _ ≤ (cap : ℝ) ^ 2 * Real.sqrt cap * R.ε * (a' / a) ^ 2 := by gcongr
        _ ≤ _ := by rwa [he]
    exact stability_of_run R ha (by rwa [hA]) hsmall

variable {K Op Tst : Type} [Inhabited K]
variable [Has ScalarOp Op] [Has Blas1Op Op] [Has OperatorOp Op] [Has CmpTst Tst]
variable [Apart Blas1Op ScalarOp Op] [Apart Blas1Op OperatorOp Op]

/-- The full rounded scalar CG program succeeds and returns an actual computed run with
backward-model, physical-energy convergence and delayed-estimation guarantees. The spectrum,
unit roundoff and cap determine every continuation guard. -/
theorem runs_solve_seq_stability {M : Machine K} {dec : K → ℝ} {em u e : ℝ}
    {n cap : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} {I : Interp Op Tst K}
    (hS : IsScalar M I) (hM : StdModel u dec M) (hA : IsMatvec dec A (em * specNorm A) I)
    (hCmp : IsCmp dec I) (hAT : Aᵀ = A) {a a' : ℝ}
    (ha : 0 < a) (hspec : spectrum ℝ A ⊆ Set.Icc a a') (hu : 0 ≤ u)
    (hem : em ≤ e) (hue : u ≤ e) (hde : (Blas.seq.err u).dot n ≤ e)
    (hae : (Blas.seq.err u).axpy ≤ e) (he : e ≤ 1 / 100)
    (hprec : 3 * e * a' ≤ a)
    (hwindow : (cap : ℝ) ^ 2 * Real.sqrt cap * e * (a' / a) ^ 2 ≤
      1 / 10 ^ 5)
    {τ : Tape K} {μ : Mem K} {b x r p v : ℕ × ℕ} {bs xs : List K}
    (hbx : b.1 ≠ x.1) (hbr : b.1 ≠ r.1) (hbp : b.1 ≠ p.1) (hbv : b.1 ≠ v.1)
    (hxr : x.1 ≠ r.1) (hxp : x.1 ≠ p.1) (hxv : x.1 ≠ v.1)
    (hrp : r.1 ≠ p.1) (hrv : r.1 ≠ v.1) (hpv : p.1 ≠ v.1)
    (hl : μ.Live [b, x, r, p, v]) (hbs : μ.store.readBlock b.1 b.2 n = some bs)
    (hxs : μ.store.readBlock x.1 x.2 n = some xs) (hx0 : decv dec n xs = 0)
    (hz : μ.Room [x, r, p, v] [n, n, n, 1]) :
    ConditionalRuns I (Blas.ws 0) τ (solve.link (Blas.seq (Op := Op) (Tst := Tst)).table)
      (Env.frame [n, cap] [b, x, x, r, p, v]) μ (seqSolveCount n cap) (2 * n + 4)
      (fun μ' => μ'.pos = μ.pos ∧
        StableOutput dec A (decv dec n bs) e a a' cap x r p v μ') := by
  have hrun := runs_solve_seq hS hM hA hCmp hAT ha hspec hu hem hue hde hae he hprec
    hwindow (τ := τ)
    hbx hbr hbp hbv hxr hxp hxv hrp hrv hpv hl hbs hxs hx0 hz
  exact hrun.mono le_rfl le_rfl fun _ h => ⟨h.1, h.2.stable ha hspec hwindow⟩

end NLAlib.Krylov.CG.HSCG.Carried.Rounded
