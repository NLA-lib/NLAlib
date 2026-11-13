/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Norms.SchattenPowers
public import NLAlib.Matrix.Norms.SchattenHolder
public import NLAlib.ForMathlib.Analysis.MeanInequalities

/-!
# Uniform smoothness of even Schatten moments

Adding and subtracting the same matrix isolates the even terms in the average of the two
Schatten moments. Schatten Hölder bounds those terms by the corresponding scalar moments.

## Main results

* `NLAlib.schattenNorm_add_pow_add_schattenNorm_sub_pow_div_rpow_le`: the two-point smoothness
  inequality for positive even exponents.
-/

@[expose] public section

open scoped Matrix ENNReal

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {l m n : Type*} [Fintype l] [Fintype m] [Fintype n]

/-- Multiplication by the next signed factor updates the even and odd parts of a product. -/
private theorem schattenNorm_mul_add_mul_le {p k : ℕ} (hp : p ≠ 0) (hk : k + 1 ≤ p)
    (A B : Matrix l m 𝕜) (U V : Matrix m n 𝕜) {u v : ℝ}
    (he : schattenNorm ((p : ℝ≥0∞) / k) (U + V) ≤ u + v)
    (ho : schattenNorm ((p : ℝ≥0∞) / k) (U - V) ≤ u - v) :
    let a := schattenNorm p A
    let b := schattenNorm p B
    schattenNorm ((p : ℝ≥0∞) / ((k + 1 : ℕ) : ℝ≥0∞)) ((A + B) * U + (A - B) * V) ≤
      (a + b) * u + (a - b) * v ∧
    schattenNorm ((p : ℝ≥0∞) / ((k + 1 : ℕ) : ℝ≥0∞)) ((A + B) * U - (A - B) * V) ≤
      (a + b) * u - (a - b) * v := by
  dsimp only
  have hp0 : (p : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr hp
  have : ENNReal.HolderTriple (p : ℝ≥0∞) (p / (k : ℝ≥0∞)) (p / ((k + 1 : ℕ) : ℝ≥0∞)) := by
    constructor
    rw [ENNReal.inv_div (.inr (ENNReal.natCast_ne_top p)) (.inr hp0),
      ENNReal.inv_div (.inr (ENNReal.natCast_ne_top p)) (.inr hp0), Nat.cast_add_one]
    simp only [div_eq_mul_inv, add_mul, one_mul, add_comm]
  have hq : (1 : ℝ≥0∞) ≤ p / ((k + 1 : ℕ) : ℝ≥0∞) := by
    rw [ENNReal.le_div_iff_mul_le (.inr hp0) (.inr (ENNReal.natCast_ne_top p)), one_mul]
    exact_mod_cast hk
  have h (X Y : Matrix m n 𝕜) (x y : ℝ)
      (hx : schattenNorm ((p : ℝ≥0∞) / k) X ≤ x) (hy : schattenNorm ((p : ℝ≥0∞) / k) Y ≤ y) :
      schattenNorm ((p : ℝ≥0∞) / ((k + 1 : ℕ) : ℝ≥0∞)) (A * X + B * Y) ≤
        schattenNorm p A * x + schattenNorm p B * y := by
    refine (schattenNorm_add_le hq _ _).trans (add_le_add ?_ ?_)
    · exact (schattenNorm_mul_le hp0 (ENNReal.div_ne_zero.mpr ⟨hp0, ENNReal.natCast_ne_top k⟩)
        A X).trans (mul_le_mul_of_nonneg_left hx (schattenNorm_nonneg _ A))
    · exact (schattenNorm_mul_le hp0 (ENNReal.div_ne_zero.mpr ⟨hp0, ENNReal.natCast_ne_top k⟩)
        B Y).trans (mul_le_mul_of_nonneg_left hy (schattenNorm_nonneg _ B))
  constructor
  · convert h (U + V) (U - V) _ _ he ho using 1
    · congr 1
      simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.mul_add, Matrix.mul_sub]
      abel
    · ring
  · convert h (U - V) (U + V) _ _ ho he using 1
    · congr 1
      simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.mul_add, Matrix.mul_sub]
      abel
    · ring

/-- For even $p=2r>0$, the sum of the $p$th Schatten moments of
$\mathbf{A}+\mathbf{B}$ and $\mathbf{A}-\mathbf{B}$ is bounded by the corresponding scalar
moments of $\|\mathbf{A}\|_{S_p}$ and $\|\mathbf{B}\|_{S_p}$. [Tropp2022, §8.5]. -/
theorem schattenNorm_add_pow_add_schattenNorm_sub_pow_le {r : ℕ} (hr : 0 < r)
    (A B : Matrix m n 𝕜) :
    schattenNorm (2 * r) (A + B) ^ (2 * r) + schattenNorm (2 * r) (A - B) ^ (2 * r) ≤
      (schattenNorm (2 * r) A + schattenNorm (2 * r) B) ^ (2 * r) +
      (schattenNorm (2 * r) A - schattenNorm (2 * r) B) ^ (2 * r) := by
  classical
  let p := 2 * r
  have hp : p ≠ 0 := mul_ne_zero two_ne_zero hr.ne'
  let a := schattenNorm (p : ℝ≥0∞) A
  let b := schattenNorm (p : ℝ≥0∞) B
  let G := (A + B)ᴴ * (A + B)
  let H := (A - B)ᴴ * (A - B)
  have bounds (j : ℕ) (hj : j ≤ r) :
      schattenNorm ((p : ℝ≥0∞) / ((2 * j : ℕ) : ℝ≥0∞)) (G ^ j + H ^ j) ≤
        (a + b) ^ (2 * j) + (a - b) ^ (2 * j) ∧
      schattenNorm ((p : ℝ≥0∞) / ((2 * j : ℕ) : ℝ≥0∞)) (G ^ j - H ^ j) ≤
        (a + b) ^ (2 * j) - (a - b) ^ (2 * j) := by
    induction j with
    | zero =>
      simp only [mul_zero, Nat.cast_zero, ENNReal.div_zero (Nat.cast_ne_zero.mpr hp), pow_zero,
        sub_self, schattenNorm_zero, le_refl, and_true]
      exact (schattenNorm_add_le (by simp : (1 : ℝ≥0∞) ≤ ⊤) _ _).trans
        (add_le_add (by rw [schattenNorm_top]; exact specNorm_one_le)
          (by rw [schattenNorm_top]; exact specNorm_one_le))
    | succ j ih =>
      obtain ⟨he, ho⟩ := ih (by omega)
      obtain ⟨he', ho'⟩ := schattenNorm_mul_add_mul_le hp (k := 2 * j) (by dsimp [p]; omega)
        A B _ _ he ho
      obtain ⟨he'', ho''⟩ := schattenNorm_mul_add_mul_le hp (k := 2 * j + 1) (by dsimp [p]; omega)
        Aᴴ Bᴴ _ _ he' ho'
      rw [schattenNorm_conjTranspose, schattenNorm_conjTranspose] at he'' ho''
      simpa only [show 2 * (j + 1) = 2 * j + 1 + 1 by omega, pow_succ',
        ← Matrix.conjTranspose_add, ← Matrix.conjTranspose_sub, ← Matrix.mul_assoc, G, H, a, b]
        using And.intro he'' ho''
  have h := (bounds r le_rfl).1
  change schattenNorm ((p : ℝ≥0∞) / p) (G ^ r + H ^ r) ≤ _ at h
  rw [ENNReal.div_self (Nat.cast_ne_zero.mpr hp) (ENNReal.natCast_ne_top p), schattenNorm_one] at h
  have ht := (RCLike.re_le_norm _).trans ((norm_trace_le_nuclearNorm (G ^ r + H ^ r)).trans h)
  simpa only [Matrix.trace_add, map_add, p, a, b, G, H, Nat.cast_mul, Nat.cast_ofNat,
    schattenNorm_two_mul_natCast_pow hr.ne'] using ht

/-- **Uniform smoothness for even Schatten moments.** For real or complex rectangular matrices
$\mathbf{A},\mathbf{B}$ of the same shape and a positive even integer $p=2r$,
$$\left(\frac{\|\mathbf{A}+\mathbf{B}\|_{S_p}^p+\|\mathbf{A}-\mathbf{B}\|_{S_p}^p}{2}
\right)^{2/p} \le \|\mathbf{A}\|_{S_p}^2+(p-1)\|\mathbf{B}\|_{S_p}^2.$$
[Tropp2022, Theorem 8.2 and §8.5], for even exponents.
Result: schatten-even-moment-smoothness -/
theorem schattenNorm_add_pow_add_schattenNorm_sub_pow_div_rpow_le {r : ℕ} (hr : 0 < r)
    (A B : Matrix m n 𝕜) :
    ((schattenNorm (2 * r) (A + B) ^ (2 * r) + schattenNorm (2 * r) (A - B) ^ (2 * r)) / 2) ^
      (r : ℝ)⁻¹ ≤ schattenNorm (2 * r) A ^ 2 + (2 * (r : ℝ) - 1) * schattenNorm (2 * r) B ^ 2 := by
  let a := schattenNorm (2 * r) A
  let b := schattenNorm (2 * r) B
  have h := schattenNorm_add_pow_add_schattenNorm_sub_pow_le hr A B
  have hbound := (div_le_div_of_nonneg_right h (by norm_num : 0 ≤ (2 : ℝ))).trans
    (Real.add_pow_add_sub_pow_le a b r)
  have hn : 0 ≤ a ^ 2 + (2 * (r : ℝ) - 1) * b ^ 2 := by
    have : (1 : ℝ) ≤ r := by exact_mod_cast hr
    exact add_nonneg (sq_nonneg a) (mul_nonneg (by linarith) (sq_nonneg b))
  apply (Real.rpow_le_rpow (div_nonneg (add_nonneg
    (pow_nonneg (schattenNorm_nonneg _ _) _) (pow_nonneg (schattenNorm_nonneg _ _) _))
    (by norm_num)) hbound (inv_nonneg.mpr (Nat.cast_nonneg r))).trans_eq
  exact Real.pow_rpow_inv_natCast hn hr.ne'

end NLAlib
