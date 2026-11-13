/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.FinitePrecision.LanczosReorthRun

/-!
# Mathematical local steps and construction of reorthogonalized Lanczos runs

The same pure local-error interface is used by both the older and operation-based program
proofs. A positive admissible prefix of these numerical witnesses constructs the existing
finite-precision run without importing an execution proof or assuming algorithm success.

## Main results

* `NLAlib.LanczosReorthImplementation.RoundedStep`: one numerical transition and local bounds.
* `NLAlib.LanczosReorthImplementation.exists_run_of_steps`: the same archived prefix as a run.
-/

@[expose] public section

namespace NLAlib.LanczosReorthImplementation

open scoped Matrix

/-- The local guarantees of one rounded step with accuracy $\varepsilon$: from the previous and
current vectors $\mathbf{v}_p$, $\mathbf{v}_c$ and the previous coefficient $\beta_p$, the
computed product $\mathbf{u}$, the updates $\mathbf{w}$ and $\mathbf{z}$, the coefficient
$\alpha$, the stored norm $\nu$ of $\mathbf{z}$, the orthogonalization output $\mathbf{z}'$ with
coefficients $\mathbf{h}$ against the basis $\mathbf{V}$ (guarantee `G`), its norm $\beta$ and
the next vector $\mathbf{v}_n$ each meet their kernel error bound. -/
structure RoundedStep {N m : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) (ε : ℝ)
    (G : Matrix (Fin N) (Fin m) ℝ → (Fin N → ℝ) → (Fin m → ℝ) → (Fin N → ℝ) → Prop)
    (V : Matrix (Fin N) (Fin m) ℝ) (vp vc vn : Fin N → ℝ) (βp α ν β : ℝ)
    (uv wv zv z' : Fin N → ℝ) (h : Fin m → ℝ) : Prop where
  /-- The product. -/
  norm_mulVec_sub_le : ‖WithLp.toLp 2 (A *ᵥ vc - uv)‖ ≤ ε * specNorm A * ‖WithLp.toLp 2 vc‖
  /-- The previous update. -/
  norm_sub_smul_sub_le : ‖WithLp.toLp 2 (uv - βp • vp - wv)‖ ≤
    ε * (‖WithLp.toLp 2 uv‖ + |βp| * ‖WithLp.toLp 2 vp‖)
  /-- The diagonal coefficient. -/
  abs_dotProduct_sub_le : |vc ⬝ᵥ wv - α| ≤ ε * ‖WithLp.toLp 2 vc‖ * ‖WithLp.toLp 2 wv‖
  /-- The projection update. -/
  norm_projection_sub_le : ‖WithLp.toLp 2 (wv - α • vc - zv)‖ ≤
    ε * (‖WithLp.toLp 2 wv‖ + |α| * ‖WithLp.toLp 2 vc‖)
  /-- The stored norm before orthogonalization is nonnegative. -/
  nu_nonneg : 0 ≤ ν
  /-- The stored norm before orthogonalization. -/
  abs_nu_sub_le : |ν - ‖WithLp.toLp 2 zv‖| ≤ ε * ‖WithLp.toLp 2 zv‖
  /-- The orthogonalization guarantee. -/
  orth : G V zv h z'
  /-- The norm after orthogonalization. -/
  abs_beta_sub_le : |β - ‖WithLp.toLp 2 z'‖| ≤ ε * ‖WithLp.toLp 2 z'‖
  /-- The normalization. -/
  norm_sub_smul_le : ‖WithLp.toLp 2 (z' - β • vn)‖ ≤ ε * ‖WithLp.toLp 2 z'‖
  /-- The next vector is nearly a unit vector unless $\beta = 0$. -/
  abs_norm_sq_sub_one_le : β ≠ 0 → |‖WithLp.toLp 2 vn‖ ^ 2 - 1| ≤ ε
  /-- The next vector is zero if $\beta = 0$. -/
  eq_zero_of_eq_zero : β = 0 → vn = 0

/-- A positive strictly admissible prefix of actual numerical step witnesses constructs the
existing reorthogonalized run with the same matrix, archived vectors and coefficients. The
initial direction is nearly unit, the previous vector/coupling are zero, and all local error
parameters are nonnegative with scalar allowance at most one percent. This is mathematical
assembly from local guarantees; it assumes no execution and changes no stopping rule. -/
theorem exists_run_of_steps {n k : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    {v : ℕ → Fin n → ℝ} {alpha beta nu : ℕ → ℝ} {ε τ η ε₁ ε₂ ε₃ : ℝ}
    (hA : Aᵀ = A) (hε₀ : 0 ≤ ε) (hε : ε ≤ 1 / 100)
    (hε₁ : 0 ≤ ε₁) (hε₂ : 0 ≤ ε₂) (hε₃ : 0 ≤ ε₃) (hk : 0 < k)
    (hv₀ : v 0 = 0) (hb₀ : beta 0 = 0) (hv₁ : |‖WithLp.toLp 2 (v 1)‖ ^ 2 - 1| ≤ ε)
    (hτ : 0 < τ) (hadm : ∀ j < k, τ * nu (j + 1) < beta (j + 1))
    (hsteps : ∀ j < k, ∃ U W Z Z' : Fin n → ℝ, ∃ H : Fin (j + 1) → ℝ,
      RoundedStep A ε (IsOrthErr η ε₁ ε₂ ε₃) (LanczosReorthRun.basisOf v (j + 1))
        (v j) (v (j + 1)) (v (j + 2)) (beta j) (alpha (j + 1)) (nu (j + 1))
        (beta (j + 1)) U W Z Z' H) :
    ∃ L : LanczosReorthRun n k, L.H = A ∧ L.v = v ∧ L.α = alpha ∧ L.β = beta ∧
      L.ν = nu ∧ L.ε = ε ∧ L.τ = τ ∧ L.η₀ = η ∧ L.ε₁ = ε₁ ∧ L.ε₂ = ε₂ ∧ L.ε₃ = ε₃ := by
  classical
  have hall : ∀ j, ∃ U W Z Z' : Fin n → ℝ, ∃ H : Fin (j + 1) → ℝ, j < k →
      RoundedStep A ε (IsOrthErr η ε₁ ε₂ ε₃) (LanczosReorthRun.basisOf v (j + 1))
        (v j) (v (j + 1)) (v (j + 2)) (beta j) (alpha (j + 1)) (nu (j + 1))
        (beta (j + 1)) U W Z Z' H := by
    intro j
    by_cases hj : j < k
    · obtain ⟨U, W, Z, Z', H, hs⟩ := hsteps j hj
      exact ⟨U, W, Z, Z', H, fun _ => hs⟩
    · exact ⟨0, 0, 0, 0, 0, fun h => (hj h).elim⟩
  choose U W Z Z' H hstep using hall
  let coef : ℕ → ℕ → ℝ := fun t i => match t with
    | 0 => 0
    | j + 1 => if hi : i < j + 1 then H j ⟨i, hi⟩ else 0
  have hcoef (j : ℕ) : (fun i : Fin (j + 1) => coef (j + 1) i) = H j := by
    funext i
    simp only [coef, dif_pos i.isLt]
  refine ⟨{
    H := A, v := v, u := fun t => U (t - 1), w := fun t => W (t - 1)
    z := fun t => Z (t - 1), z' := fun t => Z' (t - 1), α := alpha, β := beta, ν := nu
    h := coef, eu := fun t => U (t - 1) - A *ᵥ v t
    ew := fun t => W (t - 1) - (U (t - 1) - beta (t - 1) • v (t - 1))
    ez := fun t => Z (t - 1) - (W (t - 1) - alpha t • v t)
    eα := fun t => alpha t - v t ⬝ᵥ W (t - 1)
    δ := fun t => beta t • v (t + 1) - Z' (t - 1)
    ε := ε, τ := τ, η₀ := η, ε₁ := ε₁, ε₂ := ε₂, ε₃ := ε₃
    transpose_H := hA, ε_nonneg := hε₀, ε_le := hε
    ε₁_nonneg := hε₁, ε₂_nonneg := hε₂, ε₃_nonneg := hε₃
    k_pos := hk, v_zero := hv₀, β_zero := hb₀
    u_eq := fun j _ => (add_sub_cancel _ _).symm
    norm_eu_le := fun j hj => by
      simpa only [Nat.add_sub_cancel, WithLp.toLp_sub, norm_sub_rev] using
        (hstep j hj).norm_mulVec_sub_le
    w_eq := fun j _ => (add_sub_cancel _ _).symm
    norm_ew_le := fun j hj => by
      simpa only [Nat.add_sub_cancel, WithLp.toLp_sub, norm_sub_rev] using
        (hstep j hj).norm_sub_smul_sub_le
    α_eq := fun j _ => (add_sub_cancel _ _).symm
    abs_eα_le := fun j hj => by
      simpa only [Nat.add_sub_cancel, abs_sub_comm] using (hstep j hj).abs_dotProduct_sub_le
    z_eq := fun j _ => (add_sub_cancel _ _).symm
    norm_ez_le := fun j hj => by
      simpa only [Nat.add_sub_cancel, WithLp.toLp_sub, norm_sub_rev] using
        (hstep j hj).norm_projection_sub_le
    abs_ν_sub_le := fun j hj => (hstep j hj).abs_nu_sub_le
    orth_eq := fun j hj => by simpa only [Nat.add_sub_cancel, hcoef] using (hstep j hj).orth
    abs_β_sub_le := fun j hj => (hstep j hj).abs_beta_sub_le
    smul_v_eq := fun j _ => (add_sub_cancel _ _).symm
    norm_δ_le := fun j hj => by
      simpa only [Nat.add_sub_cancel, WithLp.toLp_sub, norm_sub_rev] using
        (hstep j hj).norm_sub_smul_le
    abs_norm_v_sq_sub_one_le := fun j hj₁ hj₂ => by
      rcases Nat.eq_or_lt_of_le hj₁ with rfl | hj
      · exact hv₁
      · obtain ⟨i, rfl⟩ : ∃ i, j = i + 2 := ⟨j - 2, by omega⟩
        have hi : i < k := by omega
        exact (hstep i hi).abs_norm_sq_sub_one_le
          (ne_of_gt (lt_of_le_of_lt
            (mul_nonneg hτ.le (hstep i hi).nu_nonneg) (hadm i hi)))
    admissible := hadm, τ_pos := hτ }, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end NLAlib.LanczosReorthImplementation
