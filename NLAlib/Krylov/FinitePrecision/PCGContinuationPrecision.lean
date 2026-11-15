/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.FinitePrecision.PCGContinuationSpectrum

/-!
# Cap-dependent precision for rounded PCG continuation

An explicit precision window controls the residual/direction pairing defect throughout
an existing prefix. It derives the next direction's nonbreakdown from matrix inputs.

## Main results

* `NLAlib.PCGRun.p_ne_zero_of_r_ne_zero`: input-based endpoint continuation.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib.PCGRun

private theorem coefficient_le {K T L : ℝ} (hK : 1 ≤ K) (hT : 1 ≤ T) (hL : 1 ≤ L) :
    2 + 32 * K + 2 * L + 8 * T + 2 * (64 * K) * L ≤ (512 * K * T) * L := by
  have hKT : K ≤ K * T := by nlinarith
  have hTK : T ≤ K * T := by nlinarith
  have hKT1 : 1 ≤ K * T := by nlinarith
  have hKL : K ≤ K * L := by nlinarith
  have hTL : T ≤ T * L := by nlinarith
  have hKTL : L ≤ K * T * L := by nlinarith
  have hKL' := mul_le_mul_of_nonneg_right hKT (by linarith : 0 ≤ L)
  have hTL' := mul_le_mul_of_nonneg_right hTK (by linarith : 0 ≤ L)
  nlinarith

private theorem norm_coefficient_le {K T L : ℝ} (hK : 1 ≤ K) (hT : 1 ≤ T)
    (hL : 1 ≤ L) : 8 * T + 4 * (64 * K) * L ≤ (512 * K * T) * L := by
  have hKT : K ≤ K * T := by nlinarith
  have hTK : T ≤ K * T := by nlinarith
  have hTL : T ≤ T * L := by nlinarith
  have hKL' := mul_le_mul_of_nonneg_right hKT (by linarith : 0 ≤ L)
  have hTL' := mul_le_mul_of_nonneg_right hTK (by linarith : 0 ≤ L)
  nlinarith

private theorem precision_step {e F : ℝ} (he : 0 ≤ e) (hF : 2 ≤ F) (j : ℕ) :
    2 * (e * (2 * F) ^ (j + 1)) + e * F ^ (j + 2) ≤ e * (2 * F) ^ (j + 2) := by
  have hpow : F ^ (j + 1) ≤ (2 * F) ^ (j + 1) := by gcongr; linarith
  have hpow0 : 0 ≤ (2 * F) ^ (j + 1) := by positivity
  calc
    _ = 2 * (e * (2 * F) ^ (j + 1)) + e * (F ^ (j + 1) * F) := by
      rw [show j + 2 = (j + 1) + 1 by omega, pow_succ F (j + 1)]
    _ ≤ 2 * (e * (2 * F) ^ (j + 1)) + e * ((2 * F) ^ (j + 1) * F) := by
      gcongr
    _ = (2 + F) * (e * (2 * F) ^ (j + 1)) := by ring
    _ ≤ (2 * F) * (e * (2 * F) ^ (j + 1)) :=
      mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg he hpow0)
    _ = e * (2 * F) ^ (j + 2) := by
      rw [show j + 2 = (j + 1) + 1 by omega, pow_succ (2 * F) (j + 1)]
      ring

variable {n k : ℕ} (P : PCGRun n k)

/-- The pairing defect and dimensionless norm product obey explicit geometric bounds
under separate positive spectral windows and a cap-dependent common precision window. -/
private theorem geometric_bounds {a a' m m' : ℝ}
    (ha : 0 < a) (hAs : spectrum ℝ P.A ⊆ Set.Icc a a')
    (hm : 0 < m) (hMs : spectrum ℝ P.M ⊆ Set.Icc m m')
    (hAp : 6 * P.ε * a' ≤ a) (hMp : 6 * P.ε * m' ≤ m)
    (hO : P.preconditioner.ε ≤ P.ε)
    (hsmall : P.ε * (1024 * (a' / a) * (m' / m)) ^ (k + 1) ≤ 1 / 2)
    {j : ℕ} (hj : j ≤ k) :
    |P.r j ⬝ᵥ P.p j - P.ν j| ≤
      (P.ε * (1024 * (a' / a) * (m' / m)) ^ (j + 1)) * P.ν j ∧
    ‖WithLp.toLp 2 (P.r j)‖ * ‖WithLp.toLp 2 (P.p j)‖ ≤
      (512 * (a' / a) * (m' / m)) ^ (j + 1) * P.ν j := by
  let K := a' / a
  let T := m' / m
  let F := 512 * K * T
  have hr0 := P.r_ne_zero (j := 0) P.k_pos
  obtain ⟨haa, -, -⟩ := specNorm_le_and_le_dotProduct
    (by simpa only [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]
      using P.isHermitian_A) ha.le hAs hr0
  obtain ⟨hmm, -, -⟩ := specNorm_le_and_le_dotProduct
    (by simpa only [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]
      using P.posDef_M.isHermitian) hm.le hMs hr0
  have hK : 1 ≤ K := (one_le_div ha).2 haa
  have hT : 1 ≤ T := (one_le_div hm).2 hmm
  have hF : 2 ≤ F := by dsimp [F]; nlinarith
  have hF1 : 1 ≤ F := by linarith
  have hF2 : 1 ≤ 2 * F := by linarith
  have he := P.ε_nonneg
  have hsmall' : P.ε * (2 * F) ^ (k + 1) ≤ 1 / 2 := by
    convert hsmall using 1; dsimp [F, K, T]; ring
  rw [show 1024 * (a' / a) * (m' / m) = 2 * F by dsimp [F, K, T]; ring]
  change |P.r j ⬝ᵥ P.p j - P.ν j| ≤ P.ε * (2 * F) ^ (j + 1) * P.ν j ∧
    ‖WithLp.toLp 2 (P.r j)‖ * ‖WithLp.toLp 2 (P.p j)‖ ≤ F ^ (j + 1) * P.ν j
  induction j with
  | zero =>
    have hz := P.norm_r_mul_norm_z_le hm hMs hMp hO (j := 0) (Nat.zero_le _)
    have hν := P.ν_nonneg (j := 0) (Nat.zero_le _)
    have herr := P.abs_eν_le 0 (Nat.zero_le _)
    have hTF : 4 * T ≤ F := by dsimp [F]; nlinarith
    have hzQ : ‖WithLp.toLp 2 (P.r 0)‖ * ‖WithLp.toLp 2 (P.p 0)‖ ≤ 4 * T * P.ν 0 := by
      simpa only [P.p_zero] using hz
    rw [P.dotProduct_r_p_sub_ν_zero, abs_neg]
    simp only [Nat.zero_add, pow_one]
    constructor
    · have hb := mul_le_mul_of_nonneg_right hTF (mul_nonneg he hν)
      nlinarith [mul_le_mul_of_nonneg_left hz he]
    · nlinarith
  | succ j ih =>
    have hjk : j < k := by omega
    obtain ⟨hD, hQ⟩ := ih (by omega)
    have hp : P.ε * (2 * F) ^ (j + 1) ≤ 1 / 2 := by
      exact (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hF2 (by omega)) he).trans hsmall'
    have hν := P.ν_nonneg (j := j) (by omega)
    have hDhalf : |P.r j ⬝ᵥ P.p j - P.ν j| ≤ P.ν j / 2 := by
      nlinarith [mul_le_mul_of_nonneg_right hp hν]
    have hR := P.norm_r_succ_le_mul_norm_r ha hAs hAp hjk hDhalf
    have hL : 1 ≤ F ^ (j + 1) := one_le_pow₀ hF1
    have hB : 0 ≤ 64 * K := by positivity
    have hDn := P.abs_dotProduct_r_p_sub_ν_succ_le_mul_ν ha hAs hAp hm hMs hMp hO
      hB (by positivity : 0 ≤ F ^ (j + 1))
      (by positivity : 0 ≤ P.ε * (2 * F) ^ (j + 1)) hjk hR hD hQ
    have hQn := P.norm_r_succ_mul_norm_p_succ_le hm hMs hMp hO hB
      (by positivity : 0 ≤ F ^ (j + 1)) hjk hR hQ
    have hνn := P.ν_nonneg (j := j + 1) (by omega)
    have hcoeff := coefficient_le hK hT hL
    have hqcoeff := norm_coefficient_le hK hT hL
    have hstep := precision_step he hF j
    have hcoeff' := mul_le_mul_of_nonneg_left hcoeff he
    have hbound : 2 * (P.ε * (2 * F) ^ (j + 1)) +
        P.ε * (2 + 32 * K + 2 * F ^ (j + 1) + 8 * T + 2 * (64 * K) * F ^ (j + 1)) ≤
        P.ε * (2 * F) ^ (j + 2) := by
      calc
        _ ≤ 2 * (P.ε * (2 * F) ^ (j + 1)) + P.ε * (F * F ^ (j + 1)) :=
          add_le_add (le_refl _) hcoeff'
        _ = 2 * (P.ε * (2 * F) ^ (j + 1)) + P.ε * F ^ (j + 2) := by
          rw [show j + 2 = (j + 1) + 1 by omega, pow_succ F (j + 1)]
          ring
        _ ≤ _ := hstep
    constructor
    · exact hDn.trans (mul_le_mul_of_nonneg_right hbound hνn)
    · calc
        _ ≤ (8 * T + 4 * (64 * K) * F ^ (j + 1)) * P.ν (j + 1) := hQn
        _ ≤ (F * F ^ (j + 1)) * P.ν (j + 1) :=
          mul_le_mul_of_nonneg_right hqcoeff hνn
        _ = _ := by rw [pow_succ]; ring

/-- The pairing defect throughout a prefix is bounded geometrically by the common
rounding allowance, separate positive spectral windows and the admitted precision cap. -/
theorem abs_dotProduct_r_p_sub_ν_le {a a' m m' : ℝ}
    (ha : 0 < a) (hAs : spectrum ℝ P.A ⊆ Set.Icc a a')
    (hm : 0 < m) (hMs : spectrum ℝ P.M ⊆ Set.Icc m m')
    (hAp : 6 * P.ε * a' ≤ a) (hMp : 6 * P.ε * m' ≤ m)
    (hO : P.preconditioner.ε ≤ P.ε)
    (hsmall : P.ε * (1024 * (a' / a) * (m' / m)) ^ (k + 1) ≤ 1 / 2)
    {j : ℕ} (hj : j ≤ k) :
    |P.r j ⬝ᵥ P.p j - P.ν j| ≤
      (P.ε * (1024 * (a' / a) * (m' / m)) ^ (j + 1)) * P.ν j :=
  (P.geometric_bounds ha hAs hm hMs hAp hMp hO hsmall hj).1

/-- The residual/direction norm product throughout a prefix is bounded by its computed
pairing and a geometric factor from the two positive spectral windows. -/
theorem norm_r_mul_norm_p_le {a a' m m' : ℝ}
    (ha : 0 < a) (hAs : spectrum ℝ P.A ⊆ Set.Icc a a')
    (hm : 0 < m) (hMs : spectrum ℝ P.M ⊆ Set.Icc m m')
    (hAp : 6 * P.ε * a' ≤ a) (hMp : 6 * P.ε * m' ≤ m)
    (hO : P.preconditioner.ε ≤ P.ε)
    (hsmall : P.ε * (1024 * (a' / a) * (m' / m)) ^ (k + 1) ≤ 1 / 2)
    {j : ℕ} (hj : j ≤ k) :
    ‖WithLp.toLp 2 (P.r j)‖ * ‖WithLp.toLp 2 (P.p j)‖ ≤
      (512 * (a' / a) * (m' / m)) ^ (j + 1) * P.ν j :=
  (P.geometric_bounds ha hAs hm hMs hAp hMp hO hsmall hj).2

/-- Separate positive spectral windows and an explicit cap-dependent precision window
ensure that a nonzero terminal residual has a nonzero direction. No next-step success
or trajectory-dependent margin is assumed. -/
theorem p_ne_zero_of_r_ne_zero {a a' m m' : ℝ}
    (ha : 0 < a) (hAs : spectrum ℝ P.A ⊆ Set.Icc a a')
    (hm : 0 < m) (hMs : spectrum ℝ P.M ⊆ Set.Icc m m')
    (hAp : 6 * P.ε * a' ≤ a) (hMp : 6 * P.ε * m' ≤ m)
    (hO : P.preconditioner.ε ≤ P.ε)
    (hsmall : P.ε * (1024 * (a' / a) * (m' / m)) ^ (k + 1) ≤ 1 / 2)
    (hr : P.r k ≠ 0) : P.p k ≠ 0 := by
  have hlow := P.mul_norm_sq_le_ν hm hMs hMp hO (le_refl k) hr
  have hnorm : 0 < ‖WithLp.toLp 2 (P.r k)‖ := by
    rw [norm_pos_iff]
    exact fun h => hr ((WithLp.toLp_eq_zero 2).mp h)
  have hν : 0 < P.ν k := lt_of_lt_of_le (by positivity) hlow
  have hD := P.abs_dotProduct_r_p_sub_ν_le ha hAs hm hMs
    hAp hMp hO hsmall (le_refl k)
  apply P.p_ne_zero_of_abs_dotProduct_r_p_sub_ν_le hν
  nlinarith [mul_le_mul_of_nonneg_right hsmall hν.le]

/-- The same input-based continuation guarantee holds for every prefix within an admitted
cap. The precision inequality is stated at that fixed cap, rather than at the completed
prefix length. -/
theorem p_ne_zero_of_r_ne_zero_of_le_cap {a a' m m' : ℝ} {cap : ℕ}
    (ha : 0 < a) (hAs : spectrum ℝ P.A ⊆ Set.Icc a a')
    (hm : 0 < m) (hMs : spectrum ℝ P.M ⊆ Set.Icc m m')
    (hAp : 6 * P.ε * a' ≤ a) (hMp : 6 * P.ε * m' ≤ m)
    (hO : P.preconditioner.ε ≤ P.ε) (hk : k ≤ cap)
    (hsmall : P.ε * (1024 * (a' / a) * (m' / m)) ^ (cap + 1) ≤ 1 / 2)
    (hr : P.r k ≠ 0) : P.p k ≠ 0 := by
  obtain ⟨haa, -, -⟩ := specNorm_le_and_le_dotProduct
    (by simpa only [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]
      using P.isHermitian_A) ha.le hAs hr
  obtain ⟨hmm, -, -⟩ := specNorm_le_and_le_dotProduct
    (by simpa only [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]
      using P.posDef_M.isHermitian) hm.le hMs hr
  have hK : 1 ≤ a' / a := (one_le_div ha).2 haa
  have hT : 1 ≤ m' / m := (one_le_div hm).2 hmm
  have hbase : 1 ≤ 1024 * (a' / a) * (m' / m) := by nlinarith
  have hprecision : P.ε * (1024 * (a' / a) * (m' / m)) ^ (k + 1) ≤ 1 / 2 :=
    (mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ hbase (Nat.add_le_add_right hk 1)) P.ε_nonneg).trans hsmall
  exact P.p_ne_zero_of_r_ne_zero ha hAs hm hMs hAp hMp hO hprecision hr

end NLAlib.PCGRun
