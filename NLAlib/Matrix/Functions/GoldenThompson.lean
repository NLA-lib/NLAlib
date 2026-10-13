/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Functions.TraceFunctions
public import NLAlib.Matrix.Functions.Complexification

/-!
# The Golden–Thompson inequality

For Hermitian `H` and `K`, `tr exp (H + K) ≤ tr (exp H · exp K)`. It replaces the scalar identity
`e^{h + k} = e^h e^k` in the Ahlswede–Winter approach to matrix concentration.

The proof is the classical one: the Lie product formula
`(exp (H / n) exp (K / n)) ^ n → exp (H + K)` along `n = 2 ^ k`, and the trace inequality
`tr (A B) ^ (2 ^ k) ≤ tr (A ^ (2 ^ k) B ^ (2 ^ k))` for positive semidefinite `A`, `B`. It works
over any `RCLike` field and does not use Lieb's theorem.

## Main results

* `NLAlib.re_trace_exp_add_le`: the Golden–Thompson inequality.
* `Matrix.PosDef.re_trace_exp_add_cfc_log_le`: the form `tr exp (H + log X) ≤ tr (exp H · X)`.
-/

@[expose] public section

open scoped Matrix ComplexOrder MatrixOrder Topology
open NormedSpace (exp)
open Filter

namespace NLAlib

/-! ### The Lie product formula -/

section LieProduct

variable {𝕂 𝔸 : Type*} [RCLike 𝕂] [NormedRing 𝔸]

/-- Telescoping bound for a difference of powers in a normed ring. -/
private theorem norm_pow_succ_sub_pow_succ_le {x y : 𝔸} {M : ℝ} (hx : ‖x‖ ≤ M) (hy : ‖y‖ ≤ M)
    (n : ℕ) : ‖x ^ (n + 1) - y ^ (n + 1)‖ ≤ (n + 1) * M ^ n * ‖x - y‖ := by
  have hM : 0 ≤ M := (norm_nonneg x).trans hx
  induction n with
  | zero => simp
  | succ n ih =>
    have e : x ^ (n + 1 + 1) - y ^ (n + 1 + 1) =
        x ^ (n + 1) * (x - y) + (x ^ (n + 1) - y ^ (n + 1)) * y := by
      rw [pow_succ x (n + 1), pow_succ y (n + 1)]
      noncomm_ring
    have hxn : ‖x ^ (n + 1)‖ ≤ M ^ (n + 1) :=
      (norm_pow_le' x n.succ_pos).trans (pow_le_pow_left₀ (norm_nonneg x) hx _)
    calc ‖x ^ (n + 1 + 1) - y ^ (n + 1 + 1)‖
        ≤ ‖x ^ (n + 1)‖ * ‖x - y‖ + ‖x ^ (n + 1) - y ^ (n + 1)‖ * ‖y‖ := by
          rw [e]
          exact (norm_add_le _ _).trans (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))
      _ ≤ M ^ (n + 1) * ‖x - y‖ + (n + 1) * M ^ n * ‖x - y‖ * M :=
          add_le_add (mul_le_mul_of_nonneg_right hxn (norm_nonneg _))
            (mul_le_mul ih hy (norm_nonneg _) (by positivity))
      _ = ((n + 1 : ℕ) + 1) * M ^ (n + 1) * ‖x - y‖ := by
          push_cast
          ring

variable [NormedAlgebra 𝕂 𝔸] [NormOneClass 𝔸]

/-- Two curves through `1` with the same derivative at `0` have the same limit of
`F (1 / n) ^ n`. -/
private theorem tendsto_pow_sub_pow_of_hasDerivAt {F G : 𝕂 → 𝔸} {D : 𝔸} (hF0 : F 0 = 1)
    (hG0 : G 0 = 1) (hF : HasDerivAt F D 0) (hG : HasDerivAt G D 0) :
    Tendsto (fun n : ℕ => F ((n : 𝕂)⁻¹) ^ n - G ((n : 𝕂)⁻¹) ^ n) atTop (𝓝 0) := by
  have ht : Tendsto (fun n : ℕ => ((n : 𝕂)⁻¹)) atTop (𝓝 0) := tendsto_inv_atTop_nhds_zero_nat
  obtain ⟨c₁, h₁⟩ := hF.isBigO_sub.bound
  obtain ⟨c₂, h₂⟩ := hG.isBigO_sub.bound
  have hlo : (fun t : 𝕂 => F t - G t) =o[𝓝 0] fun t : 𝕂 => t := by
    have h := hasDerivAt_iff_isLittleO.mp (hF.sub hG)
    simpa [hF0, hG0] using h
  rw [NormedAddGroup.tendsto_nhds_zero]
  intro ε hε
  set C : ℝ := max (max c₁ c₂) 0 with hC
  have hδ : 0 < ε / (2 * Real.exp C) := by positivity
  filter_upwards [ht.eventually h₁, ht.eventually h₂, ht.eventually (hlo.def hδ),
    eventually_gt_atTop 0] with n hn₁ hn₂ hn₃ hn₀
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn₀.ne'
  have hnorm : ‖((k + 1 : ℕ) : 𝕂)⁻¹‖ = ((k : ℝ) + 1)⁻¹ := by
    rw [norm_inv, RCLike.norm_natCast, Nat.cast_succ]
  rw [sub_zero, hnorm] at hn₁ hn₂
  rw [hnorm] at hn₃
  have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hM : ∀ {z : 𝔸} {c : ℝ}, c ≤ C → ‖z - 1‖ ≤ c * ((k : ℝ) + 1)⁻¹ →
      ‖z‖ ≤ 1 + C * ((k : ℝ) + 1)⁻¹ := fun {z c} hc hz => by
    have h1 : ‖z‖ ≤ ‖(1 : 𝔸)‖ + ‖z - 1‖ := by
      simpa using norm_add_le (1 : 𝔸) (z - 1)
    rw [norm_one] at h1
    have h2 : c * ((k : ℝ) + 1)⁻¹ ≤ C * ((k : ℝ) + 1)⁻¹ :=
      mul_le_mul_of_nonneg_right hc (inv_nonneg.mpr hk.le)
    linarith
  rw [hF0] at hn₁
  rw [hG0] at hn₂
  have hC0 : 0 ≤ C := le_max_right _ _
  have hpow : (1 + C * ((k : ℝ) + 1)⁻¹) ^ k ≤ Real.exp C := by
    have h1 : (1 : ℝ) ≤ 1 + C * ((k : ℝ) + 1)⁻¹ := by
      have := mul_nonneg hC0 (inv_nonneg.mpr hk.le)
      linarith
    calc (1 + C * ((k : ℝ) + 1)⁻¹) ^ k ≤ (1 + C * ((k : ℝ) + 1)⁻¹) ^ (k + 1) :=
          pow_le_pow_right₀ h1 (Nat.le_succ k)
      _ ≤ Real.exp (C * ((k : ℝ) + 1)⁻¹) ^ (k + 1) :=
          pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp (C * ((k : ℝ) + 1)⁻¹)]) _
      _ = Real.exp C := by
          rw [← Real.exp_nat_mul]
          congr 1
          push_cast
          field_simp
  have hmain := norm_pow_succ_sub_pow_succ_le
    (hM (le_max_of_le_left (le_max_left c₁ c₂)) hn₁)
    (hM (le_max_of_le_left (le_max_right c₁ c₂)) hn₂) k
  calc ‖F ((k + 1 : ℕ) : 𝕂)⁻¹ ^ (k + 1) - G ((k + 1 : ℕ) : 𝕂)⁻¹ ^ (k + 1)‖
      ≤ (k + 1) * (1 + C * ((k : ℝ) + 1)⁻¹) ^ k *
          ‖F ((k + 1 : ℕ) : 𝕂)⁻¹ - G ((k + 1 : ℕ) : 𝕂)⁻¹‖ := hmain
    _ ≤ (k + 1) * Real.exp C * (ε / (2 * Real.exp C) * ((k : ℝ) + 1)⁻¹) := by gcongr
    _ = ε / 2 := by
        field_simp
    _ < ε := half_lt_self hε

/-- **The Lie product formula**, in the form
`(exp (a / n) exp (b / n)) ^ n - exp ((a + b) / n) ^ n → 0`. -/
private theorem tendsto_exp_smul_mul_exp_smul_pow_sub [CompleteSpace 𝔸] (a b : 𝔸) :
    Tendsto (fun n : ℕ => (exp ((n : 𝕂)⁻¹ • a) * exp ((n : 𝕂)⁻¹ • b)) ^ n -
      exp ((n : 𝕂)⁻¹ • (a + b)) ^ n) atTop (𝓝 0) := by
  have hF : HasDerivAt (fun t : 𝕂 => exp (t • a) * exp (t • b))
      (exp ((0 : 𝕂) • a) * a * exp ((0 : 𝕂) • b) + exp ((0 : 𝕂) • a) * (exp ((0 : 𝕂) • b) * b))
      0 :=
    (hasDerivAt_exp_smul_const a (0 : 𝕂)).mul (hasDerivAt_exp_smul_const b (0 : 𝕂))
  have hG := hasDerivAt_exp_smul_const (a + b) (0 : 𝕂)
  simp only [zero_smul, NormedSpace.exp_zero, one_mul, mul_one] at hF hG
  exact tendsto_pow_sub_pow_of_hasDerivAt (F := fun t : 𝕂 => exp (t • a) * exp (t • b))
    (G := fun t : 𝕂 => exp (t • (a + b)))
    (by simp only [zero_smul, NormedSpace.exp_zero, one_mul])
    (by simp only [zero_smul, NormedSpace.exp_zero]) hF hG

end LieProduct

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n]

/-- The trace of a product of two positive semidefinite matrices is real and nonnegative. -/
theorem _root_.Matrix.PosSemidef.re_trace_mul_nonneg {A B : Matrix n n 𝕜} (hA : A.PosSemidef)
    (hB : B.PosSemidef) : 0 ≤ RCLike.re (A * B).trace := by
  classical
  have hS : (CFC.sqrt A)ᴴ = CFC.sqrt A := (CFC.sqrt_nonneg A).isSelfAdjoint
  have h := (hB.mul_mul_conjTranspose_same (CFC.sqrt A)).re_trace_nonneg
  rwa [hS, Matrix.trace_mul_cycle, CFC.sqrt_mul_sqrt_self A hA.nonneg] at h

/-! ### Traces of powers of a product -/

/-- `re tr (Yᴴ Z) ≤ (tr (Yᴴ Y) + tr (Zᴴ Z)) / 2`. -/
private theorem re_trace_conjTranspose_mul_le (Y Z : Matrix n n 𝕜) :
    RCLike.re (Yᴴ * Z).trace ≤ (RCLike.re (Yᴴ * Y).trace + RCLike.re (Zᴴ * Z).trace) / 2 := by
  have h := (RCLike.nonneg_iff.mp (Matrix.posSemidef_conjTranspose_mul_self (Y - Z)).trace_nonneg).1
  have hstar : RCLike.re (Zᴴ * Y).trace = RCLike.re (Yᴴ * Z).trace := by
    rw [← Matrix.conjTranspose_conjTranspose Y, ← Matrix.conjTranspose_mul,
      Matrix.trace_conjTranspose, Matrix.conjTranspose_conjTranspose, RCLike.star_def,
      RCLike.conj_re]
  rw [Matrix.conjTranspose_sub, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, Matrix.trace_sub,
    Matrix.trace_sub, Matrix.trace_sub, map_sub, map_sub, map_sub, hstar] at h
  linarith

/-- The trace of a power of a product does not depend on the order of the factors. -/
private theorem trace_mul_pow_comm [DecidableEq n] (X Y : Matrix n n 𝕜) (k : ℕ) :
    ((X * Y) ^ k).trace = ((Y * X) ^ k).trace := by
  cases k with
  | zero => rw [pow_zero, pow_zero]
  | succ k =>
    have h : ∀ j : ℕ, (X * Y) ^ (j + 1) = X * (Y * X) ^ j * Y := fun j => by
      induction j with
      | zero => rw [pow_zero, zero_add, pow_one, Matrix.mul_one]
      | succ j ih =>
        rw [pow_succ, ih, pow_succ]
        simp only [Matrix.mul_assoc]
    rw [h, Matrix.trace_mul_cycle, ← pow_succ']

/-- For `m = 2 ^ j`: `re tr X ^ (2 m) ≤ tr (Xᴴ X) ^ m` for every `X`, and
`tr (A B) ^ m ≤ tr (A ^ m B ^ m)` for positive semidefinite `A`, `B`. The two are proved
together by induction on `j`. -/
private theorem re_trace_pow_two_pow_le_aux [DecidableEq n] (j : ℕ) :
    (∀ X : Matrix n n 𝕜,
      RCLike.re (X ^ 2 ^ (j + 1)).trace ≤ RCLike.re ((Xᴴ * X) ^ 2 ^ j).trace) ∧
    ∀ A B : Matrix n n 𝕜, A.PosSemidef → B.PosSemidef →
      RCLike.re ((A * B) ^ 2 ^ j).trace ≤ RCLike.re (A ^ 2 ^ j * B ^ 2 ^ j).trace := by
  induction j with
  | zero =>
    refine ⟨fun X => ?_, fun A B _ _ => ?_⟩
    · have h := re_trace_conjTranspose_mul_le Xᴴ X
      rw [Matrix.conjTranspose_conjTranspose, Matrix.trace_mul_comm X Xᴴ] at h
      rw [zero_add, pow_one, pow_zero, pow_one, pow_two]
      linarith
    · rw [pow_zero, pow_one, pow_one, pow_one]
  | succ j ih =>
    obtain ⟨ihS, ihT⟩ := ih
    refine ⟨fun X => ?_, fun A B hA hB => ?_⟩
    · have h1 := ihS (X ^ 2)
      have h2 : (((X ^ 2)ᴴ * X ^ 2) ^ 2 ^ j).trace = ((Xᴴ * X * (X * Xᴴ)) ^ 2 ^ j).trace := by
        rw [show (X ^ 2)ᴴ * X ^ 2 = Xᴴ * (Xᴴ * X * X) by
          rw [pow_two, Matrix.conjTranspose_mul]
          simp only [Matrix.mul_assoc], trace_mul_pow_comm, Matrix.mul_assoc (Xᴴ * X)]
      have h3 := ihT (Xᴴ * X) (X * Xᴴ) (Matrix.posSemidef_conjTranspose_mul_self X)
        (Matrix.posSemidef_self_mul_conjTranspose X)
      have h4 := re_trace_conjTranspose_mul_le ((Xᴴ * X) ^ 2 ^ j) ((X * Xᴴ) ^ 2 ^ j)
      rw [((Matrix.isHermitian_conjTranspose_mul_self X).pow _).eq,
        ((Matrix.isHermitian_mul_conjTranspose_self X).pow _).eq, ← pow_add, ← pow_add,
        ← two_mul, ← pow_succ', trace_mul_pow_comm X Xᴴ] at h4
      rw [← pow_mul, ← pow_succ', h2] at h1
      linarith
    · have h1 := ihS (A * B)
      have h2 : (((A * B)ᴴ * (A * B)) ^ 2 ^ j).trace = ((A ^ 2 * B ^ 2) ^ 2 ^ j).trace := by
        rw [show (A * B)ᴴ * (A * B) = B * (A ^ 2 * B) by
          rw [Matrix.conjTranspose_mul, hA.isHermitian.eq, hB.isHermitian.eq, pow_two]
          simp only [Matrix.mul_assoc], trace_mul_pow_comm, Matrix.mul_assoc, ← pow_two]
      have h3 := ihT (A ^ 2) (B ^ 2) (hA.pow 2) (hB.pow 2)
      rw [← pow_mul, ← pow_mul, ← pow_succ'] at h3
      rw [h2] at h1
      exact h1.trans h3

variable [DecidableEq n]

/-- **The Lie product formula** for matrices. -/
private theorem tendsto_exp_smul_mul_exp_smul_pow [Nonempty n] (H K : Matrix n n 𝕜) :
    Tendsto (fun k : ℕ => (exp ((k : 𝕜)⁻¹ • H) * exp ((k : 𝕜)⁻¹ • K)) ^ k) atTop
      (𝓝 (exp (H + K))) := by
  have h : Tendsto (fun k : ℕ => (exp ((k : 𝕜)⁻¹ • H) * exp ((k : 𝕜)⁻¹ • K)) ^ k -
      exp ((k : 𝕜)⁻¹ • (H + K)) ^ k) atTop (𝓝 0) := by
    open scoped Matrix.Norms.Operator in
    exact tendsto_exp_smul_mul_exp_smul_pow_sub (𝕂 := 𝕜) H K
  have h' := h.add (tendsto_const_nhds (x := exp (H + K)))
  rw [zero_add] at h'
  refine h'.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with k hk
  rw [← Matrix.exp_nsmul, ← Nat.cast_smul_eq_nsmul 𝕜, smul_smul,
    mul_inv_cancel₀ (Nat.cast_ne_zero.mpr hk.ne'), one_smul]
  abel

/-- **The Golden–Thompson inequality.** For Hermitian `H` and `K`,
`tr exp (H + K) ≤ tr (exp H · exp K)`.
[Bhatia1997, §IX.3]; [Tropp2015, §3.1 notes].
Port of the statement of `NLAlib.golden_thompson`, there over `ℂ` and derived from Lieb's theorem
by pinching; the proof here is by the Lie product formula.
Result: golden-thompson -/
theorem re_trace_exp_add_le {H K : Matrix n n 𝕜} (hH : H.IsHermitian) (hK : K.IsHermitian) :
    RCLike.re (exp (H + K)).trace ≤ RCLike.re (exp H * exp K).trace := by
  rcases isEmpty_or_nonempty n with hn | hn
  · rw [Matrix.trace_eq_zero_of_isEmpty, Matrix.trace_eq_zero_of_isEmpty]
  have hlim : Tendsto (fun k : ℕ => RCLike.re ((exp (((2 ^ k : ℕ) : 𝕜)⁻¹ • H) *
      exp (((2 ^ k : ℕ) : 𝕜)⁻¹ • K)) ^ 2 ^ k).trace) atTop
        (𝓝 (RCLike.re (exp (H + K)).trace)) :=
    ((RCLike.continuous_re.comp (continuous_id.matrix_trace)).tendsto _).comp
      ((tendsto_exp_smul_mul_exp_smul_pow H K).comp
        (tendsto_pow_atTop_atTop_of_one_lt (one_lt_two : (1 : ℕ) < 2)))
  refine le_of_tendsto' hlim fun k => ?_
  have hc : IsSelfAdjoint (((2 ^ k : ℕ) : 𝕜)⁻¹) := by
    rw [IsSelfAdjoint, star_inv₀, star_natCast]
  have hsmul : ∀ M : Matrix n n 𝕜, exp (((2 ^ k : ℕ) : 𝕜)⁻¹ • M) ^ 2 ^ k = exp M := fun M => by
    rw [← Matrix.exp_nsmul, ← Nat.cast_smul_eq_nsmul 𝕜, smul_smul,
      mul_inv_cancel₀ (Nat.cast_ne_zero.mpr (pow_pos two_pos k).ne'), one_smul]
  have h := (re_trace_pow_two_pow_le_aux k).2 _ _ (hH.smul hc).posDef_exp.posSemidef
    (hK.smul hc).posDef_exp.posSemidef
  rwa [hsmul, hsmul] at h

/-- The Golden–Thompson inequality with a logarithm: for Hermitian `H` and positive definite
`X`, `tr exp (H + log X) ≤ tr (exp H · X)`.
Port of `NLAlib.traceExp_add_matrixLog_le`, there over `ℂ`. -/
theorem _root_.Matrix.PosDef.re_trace_exp_add_cfc_log_le {H X : Matrix n n 𝕜}
    (hH : H.IsHermitian) (hX : X.PosDef) :
    RCLike.re (exp (H + cfc Real.log X)).trace ≤ RCLike.re (exp H * X).trace := by
  have h := re_trace_exp_add_le hH (cfc_predicate Real.log X : IsSelfAdjoint (cfc Real.log X))
  rwa [hX.exp_cfc_log] at h

end NLAlib
