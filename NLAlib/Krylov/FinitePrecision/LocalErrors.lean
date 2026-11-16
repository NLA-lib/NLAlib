/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.FinitePrecision.LanczosRun
public import NLAlib.Krylov.FinitePrecision.LanczosDefects

/-!
# Local errors of a finite-precision Lanczos run

For a run `L : NLAlib.LanczosRun n k` (the recurrence in Paige's ordering A(1) with bounded local
errors and local accuracy $\varepsilon \le 1/100$), coefficient growth is bounded by an
explicit finite geometric sum. Under the additional horizon $k\varepsilon \le 1/100$, this
gives bounds linear in the step and a recurrence residual of order
$j\varepsilon\|\mathbf{H}\|_2$, with consecutive vectors nearly orthogonal in the same sense.

Steps are indexed from $0$ as the columns of the computed basis: step $j < k$ is the paper's step
$j + 1$, it reads $\mathbf{v}_{j+1}$ (`L.v (j + 1)`) and produces $\mathbf{v}_{j+2}$. The bound on
$\lvert\|\mathbf{v}_{j+1}\|^2 - 1\rvert$ is the field `NLAlib.LanczosRun.abs_norm_v_sq_sub_one_le`.

No printed source: the maintainer's draft (T. Chen, *A simple stability analysis of Lanczos in
finite precision*), `lem:coefficients` and `thm:local-errors`; constants differ.

## Main definitions

* `NLAlib.LanczosRun.recurrenceError`: the residual $\mathbf{f}$ of the three-term recurrence.
* `NLAlib.LanczosRun.adjacentInner`: the inner product $\beta\,\mathbf{v}^{\mathsf{T}}\mathbf{v}'$
  of consecutive vectors.
* `NLAlib.lanczosRecurrenceErrorFactor`, `NLAlib.lanczosAdjacentInnerFactor`: the factors of
  the two bounds at step $j$, <!-- value lanczosRecurrenceErrorFactor j --> $6(j + 1)$ and
  then <!-- value lanczosAdjacentInnerFactor j --> $7(j + 1)$.

## Main results

* `NLAlib.LanczosRun.β_le_geom_sum`: coefficient growth without a horizon assumption.
* `NLAlib.LanczosRun.β_le`, `NLAlib.LanczosRun.norm_u_le`, `NLAlib.LanczosRun.norm_w_le`,
  `NLAlib.LanczosRun.abs_α_le`, `NLAlib.LanczosRun.norm_z_le`: the a priori coefficient bounds.
* `NLAlib.LanczosRun.recurrenceError_eq`: the residual is minus the sum of the local errors.
* `NLAlib.LanczosRun.norm_recurrenceError_le`: the local error bound on the residual.
* `NLAlib.LanczosRun.abs_adjacentInner_le`: local orthogonality.
-/

@[expose] public section

namespace NLAlib

open scoped Matrix

/-- **The factor of the local error bound** of a finite-precision Lanczos run at step $j$
(`NLAlib.LanczosRun.norm_recurrenceError_le`): <!-- value lanczosRecurrenceErrorFactor j -->
$$6(j + 1) \,.$$
The maintainer's draft states the bound as $\lesssim_k \varepsilon\|\mathbf{A}\|_2$; its
formalization has the factor $700j$. -/
noncomputable irreducible_def lanczosRecurrenceErrorFactor (j : ℕ) : ℝ := 6 * ((j : ℝ) + 1)

/-- The explicit value the documentation displays: the local error factor at step $j$ is at
most <!-- value lanczosRecurrenceErrorFactor j -->$6(j + 1)$ (at present an equality). -/
theorem lanczosRecurrenceErrorFactor_le (j : ℕ) :
    lanczosRecurrenceErrorFactor j ≤ 6 * ((j : ℝ) + 1) := by
  rw [lanczosRecurrenceErrorFactor_def]

/-- **The factor of the local orthogonality bound** of a finite-precision Lanczos run at step
$j$ (`NLAlib.LanczosRun.abs_adjacentInner_le`): <!-- value lanczosAdjacentInnerFactor j -->
$$7(j + 1) \,.$$
The maintainer's draft states the bound as $\lesssim_k \varepsilon\|\mathbf{A}\|_2$; its
formalization has the factor $1200j$. -/
noncomputable irreducible_def lanczosAdjacentInnerFactor (j : ℕ) : ℝ := 7 * ((j : ℝ) + 1)

/-- The explicit value the documentation displays: the local orthogonality factor at step $j$ is
at most <!-- value lanczosAdjacentInnerFactor j -->$7(j + 1)$ (at present an equality). -/
theorem lanczosAdjacentInnerFactor_le (j : ℕ) :
    lanczosAdjacentInnerFactor j ≤ 7 * ((j : ℝ) + 1) := by
  rw [lanczosAdjacentInnerFactor_def]

namespace LanczosRun

variable {n k : ℕ} (L : LanczosRun n k)

/-! ### Elementary consequences of the interface -/

/-- Under $k\varepsilon \le 1/100$, $j\varepsilon \le 1/100$ for $j \le k$. -/
theorem mul_ε_le
    (hsmall : (k : ℝ) * L.ε ≤ 1 / 100) {j : ℕ} (hj : j ≤ k) : (j : ℝ) * L.ε ≤ 1 / 100 :=
  (mul_le_mul_of_nonneg_right (by exact_mod_cast hj) L.ε_nonneg).trans hsmall

/-- The computed vectors up to step $k$ are at most $1 + \varepsilon/2$ long:
$\|\mathbf{v}_j\| \le 1 + \varepsilon/2$ for $j \le k$ ($\mathbf{v}_0 = \mathbf{0}$). -/
theorem norm_v_le {j : ℕ} (hj : j ≤ k) : ‖WithLp.toLp 2 (L.v j)‖ ≤ 1 + L.ε / 2 := by
  rcases Nat.eq_zero_or_pos j with rfl | h1
  · rw [L.v_zero, WithLp.toLp_zero, norm_zero]
    linarith [L.ε_nonneg]
  · have h := (abs_le.mp (L.abs_norm_v_sq_sub_one_le j h1 hj)).2
    have hv := norm_nonneg (WithLp.toLp 2 (L.v j))
    nlinarith [L.ε_nonneg, sq_nonneg (L.ε / 2)]

/-! ### Relative bounds of one step -/

/-- The product of step $j$: $\|\mathbf{u}_{j+1}\| \le (1 + \varepsilon)\|\mathbf{H}\|_2
\|\mathbf{v}_{j+1}\|$. -/
private theorem norm_u_le_mul {j : ℕ} (hj : j < k) :
    ‖WithLp.toLp 2 (L.u (j + 1))‖ ≤
      (1 + L.ε) * specNorm L.H * ‖WithLp.toLp 2 (L.v (j + 1))‖ := by
  rw [L.u_eq j hj]
  refine (EuclideanSpace.norm_toLp_add_le _ _).trans ?_
  have h1 := norm_toLp_mulVec_le L.H (L.v (j + 1))
  have h2 := L.norm_eu_le j hj
  linarith

/-- The first update of step $j$:
$\|\mathbf{w}_{j+1}\| \le (1 + \varepsilon)(\|\mathbf{u}_{j+1}\| + \beta_j\|\mathbf{v}_j\|)$. -/
private theorem norm_w_le_mul {j : ℕ} (hj : j < k) :
    ‖WithLp.toLp 2 (L.w (j + 1))‖ ≤ (1 + L.ε) *
      (‖WithLp.toLp 2 (L.u (j + 1))‖ + L.β j * ‖WithLp.toLp 2 (L.v j)‖) := by
  have hβ : |L.β j| = L.β j := abs_of_nonneg (L.β_nonneg j hj.le)
  have h2 := L.norm_ew_le j hj
  rw [hβ] at h2
  rw [L.w_eq j hj]
  refine (EuclideanSpace.norm_toLp_add_le _ _).trans ?_
  have h1 := EuclideanSpace.norm_toLp_sub_le (L.u (j + 1)) (L.β j • L.v j)
  rw [WithLp.toLp_smul, norm_smul, Real.norm_eq_abs, hβ] at h1
  linarith

/-- The diagonal coefficient of step $j$:
$\lvert\alpha_{j+1}\rvert \le (1 + \varepsilon)\|\mathbf{v}_{j+1}\|\|\mathbf{w}_{j+1}\|$. -/
private theorem abs_α_le_mul {j : ℕ} (hj : j < k) :
    |L.α (j + 1)| ≤
      (1 + L.ε) * ‖WithLp.toLp 2 (L.v (j + 1))‖ * ‖WithLp.toLp 2 (L.w (j + 1))‖ := by
  rw [L.α_eq j hj]
  have h1 := EuclideanSpace.abs_dotProduct_le_norm (L.v (j + 1)) (L.w (j + 1))
  have h2 := L.abs_eα_le j hj
  have := abs_add_le (L.v (j + 1) ⬝ᵥ L.w (j + 1)) (L.eα (j + 1))
  linarith

/-- The exact projection step does not increase the norm of a vector when
$\|\mathbf{v}\|^2 \le 2$: $\|\mathbf{w} - (\mathbf{v}^{\mathsf{T}}\mathbf{w})\mathbf{v}\|
\le \|\mathbf{w}\|$. -/
private theorem norm_sub_dotProduct_smul_le {m : ℕ} (v w : Fin m → ℝ)
    (hv : ‖WithLp.toLp 2 v‖ ^ 2 ≤ 2) :
    ‖WithLp.toLp 2 (w - (v ⬝ᵥ w) • v)‖ ≤ ‖WithLp.toLp 2 w‖ := by
  have hsq : ‖WithLp.toLp 2 (w - (v ⬝ᵥ w) • v)‖ ^ 2 =
      ‖WithLp.toLp 2 w‖ ^ 2 - (2 - ‖WithLp.toLp 2 v‖ ^ 2) * (v ⬝ᵥ w) ^ 2 := by
    simp only [EuclideanSpace.norm_toLp_sq_eq_dotProduct_self, sub_dotProduct, dotProduct_sub,
      smul_dotProduct, dotProduct_smul, smul_eq_mul, dotProduct_comm w v]
    ring
  have hle : ‖WithLp.toLp 2 (w - (v ⬝ᵥ w) • v)‖ ^ 2 ≤ ‖WithLp.toLp 2 w‖ ^ 2 := by
    rw [hsq]
    nlinarith [sq_nonneg (v ⬝ᵥ w)]
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 hle

/-- The second update of step $j$: $\|\mathbf{z}_{j+1}\| \le (1 + 4\varepsilon)
\|\mathbf{w}_{j+1}\|$. -/
private theorem norm_z_le_mul {j : ℕ} (hj : j < k) :
    ‖WithLp.toLp 2 (L.z (j + 1))‖ ≤ (1 + 4 * L.ε) * ‖WithLp.toLp 2 (L.w (j + 1))‖ := by
  have heα := L.abs_eα_le j hj
  have hez := L.norm_ez_le j hj
  have hα := L.abs_α_le_mul hj
  have hz : L.z (j + 1) = (L.w (j + 1) - (L.v (j + 1) ⬝ᵥ L.w (j + 1)) • L.v (j + 1)) -
      L.eα (j + 1) • L.v (j + 1) + L.ez (j + 1) := by
    rw [L.z_eq j hj, L.α_eq j hj, add_smul]
    abel
  have hvsq : ‖WithLp.toLp 2 (L.v (j + 1))‖ ^ 2 ≤ 1 + L.ε := by
    have := (abs_le.mp (L.abs_norm_v_sq_sub_one_le (j + 1) (by omega) (by omega))).2
    linarith
  set v := L.v (j + 1)
  set w := L.w (j + 1)
  have hε0 := L.ε_nonneg
  have hε1 := L.ε_le
  have hv0 := norm_nonneg (WithLp.toLp 2 v)
  have hw0 := norm_nonneg (WithLp.toLp 2 w)
  have hproj := norm_sub_dotProduct_smul_le v w (by linarith)
  rw [hz]
  refine (EuclideanSpace.norm_toLp_add_le _ _).trans ?_
  have h3 := EuclideanSpace.norm_toLp_sub_le (w - (v ⬝ᵥ w) • v) (L.eα (j + 1) • v)
  rw [WithLp.toLp_smul, norm_smul, Real.norm_eq_abs] at h3
  -- `|eα| ‖v‖ ≤ ε ‖v‖² ‖w‖ ≤ ε (1 + ε) ‖w‖`
  have h4 : |L.eα (j + 1)| * ‖WithLp.toLp 2 v‖ ≤ L.ε * (1 + L.ε) * ‖WithLp.toLp 2 w‖ := by
    calc |L.eα (j + 1)| * ‖WithLp.toLp 2 v‖
        ≤ L.ε * ‖WithLp.toLp 2 v‖ * ‖WithLp.toLp 2 w‖ * ‖WithLp.toLp 2 v‖ := by gcongr
      _ = L.ε * ‖WithLp.toLp 2 v‖ ^ 2 * ‖WithLp.toLp 2 w‖ := by ring
      _ ≤ L.ε * (1 + L.ε) * ‖WithLp.toLp 2 w‖ := by gcongr
  -- `|α| ‖v‖ ≤ (1 + ε) ‖v‖² ‖w‖ ≤ (1 + ε)² ‖w‖`
  have h5 : |L.α (j + 1)| * ‖WithLp.toLp 2 v‖ ≤ (1 + L.ε) ^ 2 * ‖WithLp.toLp 2 w‖ := by
    calc |L.α (j + 1)| * ‖WithLp.toLp 2 v‖
        ≤ (1 + L.ε) * ‖WithLp.toLp 2 v‖ * ‖WithLp.toLp 2 w‖ * ‖WithLp.toLp 2 v‖ := by gcongr
      _ = (1 + L.ε) * ‖WithLp.toLp 2 v‖ ^ 2 * ‖WithLp.toLp 2 w‖ := by ring
      _ ≤ (1 + L.ε) * (1 + L.ε) * ‖WithLp.toLp 2 w‖ := by gcongr
      _ = (1 + L.ε) ^ 2 * ‖WithLp.toLp 2 w‖ := by ring
  have h6 : L.ε * (‖WithLp.toLp 2 w‖ + |L.α (j + 1)| * ‖WithLp.toLp 2 v‖) ≤
      L.ε * (1 + (1 + L.ε) ^ 2) * ‖WithLp.toLp 2 w‖ := by
    have := mul_le_mul_of_nonneg_left h5 hε0
    nlinarith
  have hc : L.ε * (1 + L.ε) + L.ε * (1 + (1 + L.ε) ^ 2) ≤ 4 * L.ε := by
    nlinarith [mul_nonneg hε0 (show 0 ≤ 1 - 3 * L.ε - L.ε ^ 2 by nlinarith)]
  nlinarith [mul_le_mul_of_nonneg_right hc hw0]

/-- The normalisation of step $j$: $\beta_{j+1} \le (1 + 2\varepsilon)\|\mathbf{z}_{j+1}\|$. -/
private theorem β_succ_le_mul {j : ℕ} (hj : j < k) :
    L.β (j + 1) ≤ (1 + 2 * L.ε) * ‖WithLp.toLp 2 (L.z (j + 1))‖ := by
  have hε0 := L.ε_nonneg
  have hε1 := L.ε_le
  have hz0 := norm_nonneg (WithLp.toLp 2 (L.z (j + 1)))
  have hβ0 := L.β_nonneg (j + 1) (by omega)
  rcases hβ0.eq_or_lt with hβ | hβ
  · rw [← hβ]
    positivity
  have hnext : 1 - L.ε ≤ ‖WithLp.toLp 2 (L.v (j + 2))‖ ^ 2 := by
    rcases (show j + 1 < k ∨ j + 1 = k by omega) with h | h
    · have h' := (abs_le.mp (L.abs_norm_v_sq_sub_one_le (j + 2) (by omega) (by omega))).1
      linarith
    · subst h
      have h' := (abs_le.mp (L.abs_norm_v_succ_sq_sub_one_le hβ.ne')).1
      linarith
  have heq := congrArg (fun x => ‖WithLp.toLp 2 x‖) (L.smul_v_eq j hj)
  rw [WithLp.toLp_smul, norm_smul, Real.norm_eq_abs, abs_of_pos hβ] at heq
  have hδ := L.norm_δ_le j hj
  have htri := EuclideanSpace.norm_toLp_add_le (L.z (j + 1)) (L.δ (j + 1))
  have hprod : L.β (j + 1) * ‖WithLp.toLp 2 (L.v (j + 2))‖ ≤
      (1 + L.ε) * ‖WithLp.toLp 2 (L.z (j + 1))‖ := by
    rw [heq]
    linarith
  have hv0 := norm_nonneg (WithLp.toLp 2 (L.v (j + 2)))
  have hsq : L.β (j + 1) ^ 2 * (1 - L.ε) ≤ (1 + L.ε) ^ 2 * ‖WithLp.toLp 2 (L.z (j + 1))‖ ^ 2 := by
    calc L.β (j + 1) ^ 2 * (1 - L.ε)
        ≤ L.β (j + 1) ^ 2 * ‖WithLp.toLp 2 (L.v (j + 2))‖ ^ 2 := by gcongr
      _ = (L.β (j + 1) * ‖WithLp.toLp 2 (L.v (j + 2))‖) ^ 2 := by ring
      _ ≤ ((1 + L.ε) * ‖WithLp.toLp 2 (L.z (j + 1))‖) ^ 2 := by gcongr
      _ = (1 + L.ε) ^ 2 * ‖WithLp.toLp 2 (L.z (j + 1))‖ ^ 2 := by ring
  have hc : (1 + L.ε) ^ 2 ≤ (1 + 2 * L.ε) ^ 2 * (1 - L.ε) := by
    nlinarith [mul_nonneg hε0 (show 0 ≤ 1 - L.ε - 4 * L.ε ^ 2 by nlinarith)]
  have hsq' : L.β (j + 1) ^ 2 ≤ ((1 + 2 * L.ε) * ‖WithLp.toLp 2 (L.z (j + 1))‖) ^ 2 := by
    have h1 : 0 < 1 - L.ε := by linarith
    have := mul_le_mul_of_nonneg_right hc (sq_nonneg ‖WithLp.toLp 2 (L.z (j + 1))‖)
    nlinarith
  exact (sq_le_sq₀ hβ.le (by positivity)).1 hsq'

/-- The first update in terms of $\beta_j$ alone:
$\|\mathbf{w}_{j+1}\| \le (1+\varepsilon)(1+\varepsilon/2)((1+\varepsilon)\|\mathbf{H}\|_2
+ \beta_j)$. -/
private theorem norm_w_le_β {j : ℕ} (hj : j < k) :
    ‖WithLp.toLp 2 (L.w (j + 1))‖ ≤
      (1 + L.ε) * (1 + L.ε / 2) * ((1 + L.ε) * specNorm L.H + L.β j) := by
  have hε0 := L.ε_nonneg
  have hH := specNorm_nonneg L.H
  have hβ := L.β_nonneg j hj.le
  have h1 := L.norm_w_le_mul hj
  have h2 := L.norm_u_le_mul hj
  have hv1 := L.norm_v_le (j := j + 1) (by omega)
  have hv0 := L.norm_v_le (j := j) hj.le
  have hu : ‖WithLp.toLp 2 (L.u (j + 1))‖ ≤ (1 + L.ε) * specNorm L.H * (1 + L.ε / 2) :=
    h2.trans (by gcongr)
  have hb : L.β j * ‖WithLp.toLp 2 (L.v j)‖ ≤ L.β j * (1 + L.ε / 2) := by gcongr
  calc ‖WithLp.toLp 2 (L.w (j + 1))‖
      ≤ (1 + L.ε) * (‖WithLp.toLp 2 (L.u (j + 1))‖ + L.β j * ‖WithLp.toLp 2 (L.v j)‖) := h1
    _ ≤ (1 + L.ε) * ((1 + L.ε) * specNorm L.H * (1 + L.ε / 2) + L.β j * (1 + L.ε / 2)) := by
        gcongr
    _ = _ := by ring

/-- The recurrence data of a run: its matrix, vectors and coefficients. -/
def toLanczosData : LanczosData n k :=
  ⟨L.H, L.v, L.α, L.β, L.transpose_H, L.k_pos, L.v_zero, L.β_zero⟩

/-- The **residual of the three-term recurrence** at step $j$ (0-based):
$\mathbf{f}_j = \mathbf{H}\mathbf{v}_{j+1} - \beta_j\mathbf{v}_j - \alpha_{j+1}\mathbf{v}_{j+1}
- \beta_{j+1}\mathbf{v}_{j+2}$, the paper's $\mathbf{f}_{j+1}$. -/
noncomputable def recurrenceError (j : ℕ) : Fin n → ℝ :=
  L.toLanczosData.recurrenceError j

/-- The **inner product of consecutive Lanczos vectors** at step $j$ (0-based):
$\mathbf{v}_{j+1}^{\mathsf{T}}(\beta_{j+1}\mathbf{v}_{j+2})$, the paper's $p_{j+1}$. -/
noncomputable def adjacentInner (j : ℕ) : ℝ :=
  L.toLanczosData.adjacentInner j

/-! ### A priori coefficient bounds -/

/-- A single coefficient step, retaining its local growth factor. -/
theorem β_succ_le {j : ℕ} (hj : j < k) :
    L.β (j + 1) ≤ (1 + 8 * L.ε) * ((1 + L.ε) * specNorm L.H + L.β j) := by
  have hε0 := L.ε_nonneg
  have hε1 := L.ε_le
  have hβ := L.β_nonneg j hj.le
  have h1 := L.β_succ_le_mul hj
  have h2 := L.norm_z_le_mul hj
  have h3 := L.norm_w_le_β hj
  have hc : (1 + 2 * L.ε) * ((1 + 4 * L.ε) * ((1 + L.ε) * (1 + L.ε / 2))) ≤
      1 + 8 * L.ε := by
    nlinarith [mul_nonneg hε0
      (show 0 ≤ 1 / 2 - 35 / 2 * L.ε - 15 * L.ε ^ 2 - 4 * L.ε ^ 3 by nlinarith)]
  calc L.β (j + 1)
      ≤ (1 + 2 * L.ε) * ((1 + 4 * L.ε) *
          ((1 + L.ε) * (1 + L.ε / 2) * ((1 + L.ε) * specNorm L.H + L.β j))) := by
        refine h1.trans ?_
        gcongr
        exact h2.trans (by gcongr)
    _ = ((1 + 2 * L.ε) * ((1 + 4 * L.ε) * ((1 + L.ε) * (1 + L.ε / 2)))) *
        ((1 + L.ε) * specNorm L.H + L.β j) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hc (by positivity)

/-- A diagonal coefficient is controlled by the matrix norm and the previous off-diagonal
coefficient, using local accuracy alone. -/
theorem abs_α_le_β {j : ℕ} (hj : j < k) :
    |L.α (j + 1)| ≤ 2 * (specNorm L.H + L.β j) := by
  have hε0 := L.ε_nonneg
  have hε1 := L.ε_le
  have hβ := L.β_nonneg j hj.le
  have hH := specNorm_nonneg L.H
  have hα := L.abs_α_le_mul hj
  have hv := L.norm_v_le (by omega : j + 1 ≤ k)
  have hw := L.norm_w_le_β hj
  calc |L.α (j + 1)|
      ≤ (1 + L.ε) * (1 + L.ε / 2) *
          ((1 + L.ε) * (1 + L.ε / 2) * ((1 + L.ε) * specNorm L.H + L.β j)) := by
        refine hα.trans ?_
        gcongr
    _ ≤ (101 / 100 : ℝ) * (201 / 200) *
          ((101 / 100) * (201 / 200) * ((101 / 100) * specNorm L.H + L.β j)) := by
        gcongr <;> linarith only [hε1]
    _ ≤ _ := by nlinarith only [hH, hβ]

/-- The coefficient bound with accumulated growth retained as a finite geometric sum.
Only local accuracy is assumed; the formula includes $\varepsilon=0$ without division.
No printed source. This is the unrolling of `NLAlib.LanczosRun.β_succ_le`. -/
theorem β_le_geom_sum {j : ℕ} (hj : j ≤ k) :
    L.β j ≤ (1 + L.ε) * specNorm L.H *
      ∑ i ∈ Finset.range j, (1 + 8 * L.ε) ^ (i + 1) := by
  have hε := L.ε_nonneg
  induction j with
  | zero => simp [L.β_zero]
  | succ j ih =>
    have hi := ih (Nat.le_of_succ_le hj)
    have hstep := L.β_succ_le (Nat.lt_of_succ_le hj)
    set q := 1 + 8 * L.ε with hq
    have hq0 : 0 ≤ q := by positivity
    have hs : ∑ i ∈ Finset.range (j + 1), q ^ (i + 1) =
        q * (1 + ∑ i ∈ Finset.range j, q ^ (i + 1)) := by
      rw [Finset.sum_range_succ']
      simp only [zero_add, pow_one]
      rw [mul_add, mul_one, Finset.mul_sum, add_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      rw [pow_succ']
    calc L.β (j + 1)
        ≤ q * ((1 + L.ε) * specNorm L.H +
            (1 + L.ε) * specNorm L.H * ∑ i ∈ Finset.range j, q ^ (i + 1)) := by
          exact hstep.trans (mul_le_mul_of_nonneg_left (add_le_add le_rfl hi) hq0)
      _ = (1 + L.ε) * specNorm L.H * ∑ i ∈ Finset.range (j + 1), q ^ (i + 1) := by
          rw [hs]
          ring

/-- **The off-diagonal coefficients grow at most linearly**
(assuming $k\varepsilon \le 1/100$): for $j \le k$,
$\beta_j \le \tfrac54\, j\,\|\mathbf{H}\|_2$.
No printed source; the maintainer's draft, `lem:coefficients`, proves
$\beta_j \le 4j\|\mathbf{A}\|_2$ (Step 3); the recurrence
$\beta_j \le (1 + 8\varepsilon)(\beta_{j-1} + (1+\varepsilon)
\|\mathbf{H}\|_2)$ used here carries less slack. -/
theorem β_le
    (hsmall : (k : ℝ) * L.ε ≤ 1 / 100) {j : ℕ} (hj : j ≤ k) : L.β j ≤ 5 / 4 * j * specNorm L.H := by
  induction j with
  | zero => simp [L.β_zero]
  | succ j ih =>
    have hjk : j < k := by omega
    have hε0 := L.ε_nonneg
    have hε1 := L.ε_le
    have hH := specNorm_nonneg L.H
    have hβ := L.β_nonneg j hjk.le
    have hjε := L.mul_ε_le hsmall hjk.le
    have ih := ih hjk.le
    have hstep := L.β_succ_le hjk
    have h8 : 8 * L.ε * L.β j ≤ 1 / 10 * specNorm L.H := by
      calc 8 * L.ε * L.β j ≤ 8 * L.ε * (5 / 4 * j * specNorm L.H) := by gcongr
        _ = 10 * (j * L.ε) * specNorm L.H := by ring
        _ ≤ 10 * (1 / 100) * specNorm L.H := by gcongr
        _ = 1 / 10 * specNorm L.H := by norm_num
    have h9 : (1 + 8 * L.ε) * (1 + L.ε) * specNorm L.H ≤ 11 / 10 * specNorm L.H := by
      gcongr
      nlinarith
    push_cast
    nlinarith

/-- **The computed products are bounded**: for $j < k$,
$\|\mathbf{u}_{j+1}\| \le \tfrac{21}{20}\|\mathbf{H}\|_2$.
No printed source; the maintainer's draft, `lem:coefficients` (Step 2), prints
$2\|\mathbf{A}\|_2$. -/
theorem norm_u_le {j : ℕ} (hj : j < k) :
    ‖WithLp.toLp 2 (L.u (j + 1))‖ ≤ 21 / 20 * specNorm L.H := by
  have hε0 := L.ε_nonneg
  have hε1 := L.ε_le
  have hH := specNorm_nonneg L.H
  calc ‖WithLp.toLp 2 (L.u (j + 1))‖
      ≤ (1 + L.ε) * specNorm L.H * ‖WithLp.toLp 2 (L.v (j + 1))‖ := L.norm_u_le_mul hj
    _ ≤ (1 + L.ε) * specNorm L.H * (1 + L.ε / 2) := by gcongr; exact L.norm_v_le (by omega)
    _ = (1 + L.ε) * (1 + L.ε / 2) * specNorm L.H := by ring
    _ ≤ 21 / 20 * specNorm L.H := by gcongr; nlinarith

/-- **The first updates are bounded** (assuming $k\varepsilon \le 1/100$): for $j < k$,
$\|\mathbf{w}_{j+1}\| \le \tfrac54 (j + 1)\|\mathbf{H}\|_2$.
No printed source; the maintainer's draft, `lem:coefficients` (Step 4), prints $5j\|\mathbf{A}\|_2$
in its 1-based indexing. -/
theorem norm_w_le (hsmall : (k : ℝ) * L.ε ≤ 1 / 100) {j : ℕ} (hj : j < k) :
    ‖WithLp.toLp 2 (L.w (j + 1))‖ ≤ 5 / 4 * (j + 1) * specNorm L.H := by
  have hε0 := L.ε_nonneg
  have hε1 := L.ε_le
  have hH := specNorm_nonneg L.H
  have hjε := L.mul_ε_le hsmall hj.le
  have hβ := L.β_le hsmall hj.le
  have ha : (1 + L.ε) * (1 + L.ε / 2) ≤ 1 + 8 / 5 * L.ε := by nlinarith
  have hj0 : (0 : ℝ) ≤ j := j.cast_nonneg
  have hβ0 := L.β_nonneg j hj.le
  calc ‖WithLp.toLp 2 (L.w (j + 1))‖
      ≤ (1 + L.ε) * (1 + L.ε / 2) * ((1 + L.ε) * specNorm L.H + L.β j) := L.norm_w_le_β hj
    _ ≤ (1 + 8 / 5 * L.ε) * ((1 + L.ε) * specNorm L.H + 5 / 4 * j * specNorm L.H) := by
        gcongr
    _ = (1 + 8 / 5 * L.ε) * (1 + L.ε) * specNorm L.H + 5 / 4 * j * specNorm L.H +
          2 * (j * L.ε) * specNorm L.H := by ring
    _ ≤ 21 / 20 * specNorm L.H + 5 / 4 * j * specNorm L.H + 2 * (1 / 100) * specNorm L.H := by
        gcongr
        nlinarith
    _ ≤ 5 / 4 * (j + 1) * specNorm L.H := by nlinarith

/-- **The diagonal coefficients are bounded** (assuming $k\varepsilon \le 1/100$): for $j < k$,
$\lvert\alpha_{j+1}\rvert \le \tfrac43 (j + 1)\|\mathbf{H}\|_2$.
No printed source; the maintainer's draft, `lem:coefficients` (Step 4), prints
$6j\|\mathbf{A}\|_2$ in its 1-based indexing. -/
theorem abs_α_le
    (hsmall : (k : ℝ) * L.ε ≤ 1 / 100)
    {j : ℕ} (hj : j < k) : |L.α (j + 1)| ≤ 4 / 3 * (j + 1) * specNorm L.H := by
  have hε0 := L.ε_nonneg
  have hε1 := L.ε_le
  have hH := specNorm_nonneg L.H
  calc |L.α (j + 1)|
      ≤ (1 + L.ε) * ‖WithLp.toLp 2 (L.v (j + 1))‖ * ‖WithLp.toLp 2 (L.w (j + 1))‖ :=
        L.abs_α_le_mul hj
    _ ≤ (1 + L.ε) * (1 + L.ε / 2) * (5 / 4 * (j + 1) * specNorm L.H) := by
        gcongr
        · exact L.norm_v_le (by omega)
        · exact L.norm_w_le hsmall hj
    _ ≤ 16 / 15 * (5 / 4 * (j + 1) * specNorm L.H) := by gcongr; nlinarith
    _ = 4 / 3 * (j + 1) * specNorm L.H := by ring

/-- **The unnormalised next vectors are bounded** (assuming $k\varepsilon \le 1/100$): for $j < k$,
$\|\mathbf{z}_{j+1}\| \le \tfrac43 (j + 1)\|\mathbf{H}\|_2$.
No printed source; the maintainer's draft, `lem:coefficients` (Step 4), prints
$7j\|\mathbf{A}\|_2$ in its 1-based indexing. -/
theorem norm_z_le (hsmall : (k : ℝ) * L.ε ≤ 1 / 100) {j : ℕ} (hj : j < k) :
    ‖WithLp.toLp 2 (L.z (j + 1))‖ ≤ 4 / 3 * (j + 1) * specNorm L.H := by
  have hε1 := L.ε_le
  have hH := specNorm_nonneg L.H
  calc ‖WithLp.toLp 2 (L.z (j + 1))‖
      ≤ (1 + 4 * L.ε) * ‖WithLp.toLp 2 (L.w (j + 1))‖ := L.norm_z_le_mul hj
    _ ≤ (1 + 4 * L.ε) * (5 / 4 * (j + 1) * specNorm L.H) := by
        gcongr
        · linarith [L.ε_nonneg]
        · exact L.norm_w_le hsmall hj
    _ ≤ 16 / 15 * (5 / 4 * (j + 1) * specNorm L.H) := by gcongr; linarith
    _ = 4 / 3 * (j + 1) * specNorm L.H := by ring

/-! ### Local error bounds -/

/-- The residual of the recurrence is minus the sum of the four vector local errors:
$\mathbf{f}_j = -(\mathbf{e}^u_{j+1} + \mathbf{e}^w_{j+1} + \mathbf{e}^z_{j+1}
+ \boldsymbol{\delta}_{j+1})$ for $j < k$. -/
theorem recurrenceError_eq {j : ℕ} (hj : j < k) :
    L.recurrenceError j = -(L.eu (j + 1) + L.ew (j + 1) + L.ez (j + 1) + L.δ (j + 1)) := by
  exact L.toLanczosData.recurrenceError_eq_of_eq j
    (L.u (j + 1)) (L.w (j + 1)) (L.z (j + 1))
    (L.eu (j + 1)) (L.ew (j + 1)) (L.ez (j + 1)) (L.δ (j + 1))
    (L.u_eq j hj) (L.w_eq j hj) (L.z_eq j hj) (L.smul_v_eq j hj)

/-- **Local error bound for finite-precision Lanczos**
(assuming $k\varepsilon \le 1/100$) (Paige): the computed vectors satisfy the
three-term recurrence up to a small residual, for $j <
k$, <!-- value lanczosRecurrenceErrorFactor j -->
$$\|\mathbf{H}\mathbf{v}_{j+1} - \beta_j\mathbf{v}_j - \alpha_{j+1}\mathbf{v}_{j+1} -
\beta_{j+1}\mathbf{v}_{j+2}\| \le 6(j + 1)\,\varepsilon\,\|\mathbf{H}\|_2 \,.$$
No printed source; the maintainer's draft, `thm:local-errors`, states
$\|\mathbf{f}_j\| \lesssim_k \varepsilon\|\mathbf{A}\|_2$ (its formalization: $700j$); the
constant here comes from the sharper coefficient bounds. [Paige1976, §2–3] has bounds of this
kind, from floating-point arithmetic directly.
Result: lanczos-local-errors -/
theorem norm_recurrenceError_le (hsmall : (k : ℝ) * L.ε ≤ 1 / 100) {j : ℕ} (hj : j < k) :
    ‖WithLp.toLp 2 (L.recurrenceError j)‖ ≤
      lanczosRecurrenceErrorFactor j * L.ε * specNorm L.H := by
  rw [lanczosRecurrenceErrorFactor_def]
  have hε0 := L.ε_nonneg
  have hε1 := L.ε_le
  have hH := specNorm_nonneg L.H
  have hj0 : (0 : ℝ) ≤ j := j.cast_nonneg
  set a := 1 + L.ε / 2 with ha_def
  have ha : a ≤ 201 / 200 := by rw [ha_def]; linarith
  have ha0 : 0 ≤ a := by positivity
  have hv1 : ‖WithLp.toLp 2 (L.v (j + 1))‖ ≤ a := L.norm_v_le (by omega)
  have hv0 : ‖WithLp.toLp 2 (L.v j)‖ ≤ a := L.norm_v_le hj.le
  have hβ : |L.β j| ≤ 5 / 4 * j * specNorm L.H := by
    rw [abs_of_nonneg (L.β_nonneg j hj.le)]
    exact L.β_le hsmall hj.le
  have hu := L.norm_u_le hj
  have hw := L.norm_w_le hsmall hj
  have hα := L.abs_α_le hsmall hj
  have hz := L.norm_z_le hsmall hj
  have heu : ‖WithLp.toLp 2 (L.eu (j + 1))‖ ≤ L.ε * (specNorm L.H * a) :=
    (L.norm_eu_le j hj).trans (by rw [mul_assoc]; gcongr)
  have hew : ‖WithLp.toLp 2 (L.ew (j + 1))‖ ≤
      L.ε * (21 / 20 * specNorm L.H + 5 / 4 * j * specNorm L.H * a) :=
    (L.norm_ew_le j hj).trans (by gcongr)
  have hez : ‖WithLp.toLp 2 (L.ez (j + 1))‖ ≤
      L.ε * (5 / 4 * (j + 1) * specNorm L.H + 4 / 3 * (j + 1) * specNorm L.H * a) :=
    (L.norm_ez_le j hj).trans (by gcongr)
  have hδ : ‖WithLp.toLp 2 (L.δ (j + 1))‖ ≤ L.ε * (4 / 3 * (j + 1) * specNorm L.H) :=
    (L.norm_δ_le j hj).trans (by gcongr)
  have hsum : ‖WithLp.toLp 2 (L.eu (j + 1) + L.ew (j + 1) + L.ez (j + 1) + L.δ (j + 1))‖ ≤
      ‖WithLp.toLp 2 (L.eu (j + 1))‖ + ‖WithLp.toLp 2 (L.ew (j + 1))‖ +
        ‖WithLp.toLp 2 (L.ez (j + 1))‖ + ‖WithLp.toLp 2 (L.δ (j + 1))‖ := by
    refine (EuclideanSpace.norm_toLp_add_le _ _).trans ?_
    gcongr
    refine (EuclideanSpace.norm_toLp_add_le _ _).trans ?_
    gcongr
    exact EuclideanSpace.norm_toLp_add_le _ _
  have hX : 0 ≤ (1 + 5 / 4 * j + 4 / 3 * (j + 1)) * specNorm L.H := by positivity
  have hY : a * ((1 + 5 / 4 * j + 4 / 3 * (j + 1)) * specNorm L.H) ≤
      201 / 200 * ((1 + 5 / 4 * j + 4 / 3 * (j + 1)) * specNorm L.H) := by gcongr
  rw [L.recurrenceError_eq hj, WithLp.toLp_neg, norm_neg]
  refine hsum.trans ?_
  have hfin : specNorm L.H * a + (21 / 20 * specNorm L.H + 5 / 4 * j * specNorm L.H * a) +
      (5 / 4 * (j + 1) * specNorm L.H + 4 / 3 * (j + 1) * specNorm L.H * a) +
      4 / 3 * (j + 1) * specNorm L.H ≤ 6 * (j + 1) * specNorm L.H := by
    nlinarith
  nlinarith [mul_le_mul_of_nonneg_left hfin hε0]

/-- The inner product of consecutive vectors in terms of the local errors: for $j < k$,
$p_j = -e^\alpha_{j+1} - (\|\mathbf{v}_{j+1}\|^2 - 1)\alpha_{j+1}
+ \mathbf{v}_{j+1}^{\mathsf{T}}\mathbf{e}^z_{j+1} + \mathbf{v}_{j+1}^{\mathsf{T}}
\boldsymbol{\delta}_{j+1}$. -/
theorem adjacentInner_eq {j : ℕ} (hj : j < k) :
    L.adjacentInner j = -L.eα (j + 1) - (‖WithLp.toLp 2 (L.v (j + 1))‖ ^ 2 - 1) * L.α (j + 1)
      + L.v (j + 1) ⬝ᵥ L.ez (j + 1) + L.v (j + 1) ⬝ᵥ L.δ (j + 1) := by
  exact L.toLanczosData.adjacentInner_eq_of_eq j
    (L.w (j + 1)) (L.z (j + 1)) (L.ez (j + 1)) (L.δ (j + 1)) (L.eα (j + 1))
    (L.α_eq j hj) (L.z_eq j hj) (L.smul_v_eq j hj)

/-- **Local orthogonality of finite-precision Lanczos**
(assuming $k\varepsilon \le 1/100$) (Paige): consecutive computed vectors
are nearly orthogonal, for $j < k$, <!-- value lanczosAdjacentInnerFactor j -->
$$\lvert\beta_{j+1}\,\mathbf{v}_{j+1}^{\mathsf{T}}\mathbf{v}_{j+2}\rvert
\le 7(j + 1)\,\varepsilon\,\|\mathbf{H}\|_2 \,.$$
No printed source; the maintainer's draft, `thm:local-errors`, states
$\lvert p_j\rvert \lesssim_k \varepsilon\|\mathbf{A}\|_2$ (its formalization: $1200j$).
Result: lanczos-local-orthogonality -/
theorem abs_adjacentInner_le (hsmall : (k : ℝ) * L.ε ≤ 1 / 100) {j : ℕ} (hj : j < k) :
    |L.adjacentInner j| ≤ lanczosAdjacentInnerFactor j * L.ε * specNorm L.H := by
  rw [lanczosAdjacentInnerFactor_def]
  have hε0 := L.ε_nonneg
  have hH := specNorm_nonneg L.H
  set a := 1 + L.ε / 2 with ha_def
  have ha : a ≤ 201 / 200 := by rw [ha_def]; linarith [L.ε_le]
  have hv1 : ‖WithLp.toLp 2 (L.v (j + 1))‖ ≤ a := L.norm_v_le (by omega)
  have hw := L.norm_w_le hsmall hj
  have hα := L.abs_α_le hsmall hj
  have hz := L.norm_z_le hsmall hj
  have hg : |‖WithLp.toLp 2 (L.v (j + 1))‖ ^ 2 - 1| ≤ L.ε :=
    L.abs_norm_v_sq_sub_one_le (j + 1) (by omega) (by omega)
  set W := 5 / 4 * (j + 1) * specNorm L.H
  set A := 4 / 3 * (j + 1) * specNorm L.H
  have hW : 0 ≤ W := by positivity
  have hA : 0 ≤ A := by positivity
  have h1 : |L.eα (j + 1)| ≤ L.ε * (a * W) :=
    (L.abs_eα_le j hj).trans (by rw [mul_assoc]; gcongr)
  have h2 : |(‖WithLp.toLp 2 (L.v (j + 1))‖ ^ 2 - 1) * L.α (j + 1)| ≤ L.ε * A := by
    rw [abs_mul]
    gcongr
  have h3 : |L.v (j + 1) ⬝ᵥ L.ez (j + 1)| ≤ a * (L.ε * (W + A * a)) :=
    (EuclideanSpace.abs_dotProduct_le_norm _ _).trans
      (mul_le_mul hv1 ((L.norm_ez_le j hj).trans (by gcongr)) (norm_nonneg _) (by positivity))
  have h4 : |L.v (j + 1) ⬝ᵥ L.δ (j + 1)| ≤ a * (L.ε * A) :=
    (EuclideanSpace.abs_dotProduct_le_norm _ _).trans
      (mul_le_mul hv1 ((L.norm_δ_le j hj).trans (by gcongr)) (norm_nonneg _) (by positivity))
  rw [L.adjacentInner_eq hj]
  have htri := abs_add_le (-L.eα (j + 1) - (‖WithLp.toLp 2 (L.v (j + 1))‖ ^ 2 - 1) * L.α (j + 1)
    + L.v (j + 1) ⬝ᵥ L.ez (j + 1)) (L.v (j + 1) ⬝ᵥ L.δ (j + 1))
  have htri2 := abs_add_le (-L.eα (j + 1) - (‖WithLp.toLp 2 (L.v (j + 1))‖ ^ 2 - 1) *
    L.α (j + 1)) (L.v (j + 1) ⬝ᵥ L.ez (j + 1))
  have htri3 := abs_sub (-L.eα (j + 1)) ((‖WithLp.toLp 2 (L.v (j + 1))‖ ^ 2 - 1) * L.α (j + 1))
  rw [abs_neg] at htri3
  have hfin : a * W + A + a * (W + A * a) + a * A ≤ 7 * (j + 1) * specNorm L.H := by
    have h5 : a * W ≤ 201 / 200 * W := by gcongr
    have h6 : a * (W + A * a) ≤ 201 / 200 * (W + A * (201 / 200)) := by gcongr
    have h7 : a * A ≤ 201 / 200 * A := by gcongr
    simp only [W, A] at h5 h6 h7 ⊢
    nlinarith
  nlinarith [mul_le_mul_of_nonneg_left hfin hε0]

end LanczosRun

end NLAlib
