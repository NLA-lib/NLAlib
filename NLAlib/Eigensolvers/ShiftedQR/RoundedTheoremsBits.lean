/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.ShiftedQR.RoundedParameters
public import NLAlib.Eigensolvers.ShiftedQR.RoundedParameterChoices

/-!
# The bits of precision of the rounded shifted QR algorithm

The precision threshold `NLAlib.ShiftedQR.uShQR` is at least a power $Y^{-(53k + 40)}$ of the
scale-invariant argument $Y = 4(n + 1)B\Sigma^2/(\delta\min(\Gamma, \Sigma)\varphi)$ of
[BanksGarzaVargasSrivastava2022, Theorem 1.4], corrected: the printed argument
$nB/(\delta\Gamma\varphi)$ is not invariant under scaling of the input, as $\delta$ and $\Gamma$
are absolute, and Optimal's rounding constant ([BanksGarzaVargasSrivastava2022, Lemma 4.5]) is
$kn^{3/2}$ in place of $2n^2$. Every term of the threshold is a product of powers of ratios that are
each at least a fixed power of $Y$; the predicates `NLAlib.ShiftedQR.LoBd` and
`NLAlib.ShiftedQR.HiBd` track those powers.

## Main definitions

* `NLAlib.ShiftedQR.LoBd`, `NLAlib.ShiftedQR.HiBd`: $x \ge Y^{-e}$ and $x \le Y^e$.

## Main results

* `NLAlib.ShiftedQR.one_le_uShQR_mul`: $\boldsymbol{u}_{\mathrm{ShQR}} \ge Y^{-(53k + 40)}$.
-/

@[expose] public section

namespace NLAlib.ShiftedQR

open Real

/-! ### Polynomial bounds in a base `Y` -/

/-- `x` is positive and at least `Y ^ (-e)`. -/
def LoBd (Y : ℝ) (e : ℕ) (x : ℝ) : Prop := 0 < x ∧ 1 ≤ x * Y ^ e

/-- `x` is positive and at most `Y ^ e`. -/
def HiBd (Y : ℝ) (e : ℕ) (x : ℝ) : Prop := 0 < x ∧ x ≤ Y ^ e

namespace LoBd

variable {Y x y : ℝ} {a b : ℕ}

theorem pos (h : LoBd Y a x) : 0 < x := h.1

theorem mul (hx : LoBd Y a x) (hy : LoBd Y b y) : LoBd Y (a + b) (x * y) :=
  ⟨mul_pos hx.1 hy.1, by
    rw [pow_add]
    calc (1 : ℝ) ≤ (x * Y ^ a) * (y * Y ^ b) := one_le_mul_of_one_le_of_one_le hx.2 hy.2
      _ = x * y * (Y ^ a * Y ^ b) := by ring⟩

theorem div (hx : LoBd Y a x) (hy : HiBd Y b y) : LoBd Y (a + b) (x / y) :=
  ⟨div_pos hx.1 hy.1, by
    rw [pow_add]
    have h1 : 1 ≤ Y ^ b / y := by rw [le_div_iff₀ hy.1]; linarith [hy.2]
    calc (1 : ℝ) ≤ (x * Y ^ a) * (Y ^ b / y) := one_le_mul_of_one_le_of_one_le hx.2 h1
      _ = x / y * (Y ^ a * Y ^ b) := by field_simp [hy.1.ne']⟩

theorem pow (hx : LoBd Y a x) (m : ℕ) : LoBd Y (a * m) (x ^ m) :=
  ⟨pow_pos hx.1 m, by rw [pow_mul, ← mul_pow]; exact one_le_pow₀ hx.2⟩

theorem mono (hY : 1 ≤ Y) (hx : LoBd Y a x) (hab : a ≤ b) : LoBd Y b x :=
  ⟨hx.1, hx.2.trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hY hab) hx.1.le)⟩

theorem of_le (hx : LoBd Y a x) (hxy : x ≤ y) : LoBd Y a y :=
  ⟨hx.1.trans_le hxy, hx.2.trans (mul_le_mul_of_nonneg_right hxy
    (pos_of_mul_pos_right (by linarith [hx.2] : 0 < x * Y ^ a) hx.1.le).le)⟩

theorem min (hx : LoBd Y a x) (hy : LoBd Y a y) : LoBd Y a (Min.min x y) := by
  rcases min_choice x y with h | h <;> rw [h]
  exacts [hx, hy]

theorem sqrt (hY : 1 ≤ Y) (hx : LoBd Y a x) : LoBd Y a (√x) := by
  refine ⟨Real.sqrt_pos.mpr hx.1, ?_⟩
  have hYa : 1 ≤ Y ^ a := one_le_pow₀ hY
  calc (1 : ℝ) ≤ √(x * Y ^ a) := Real.one_le_sqrt.mpr hx.2
    _ = √x * √(Y ^ a) := Real.sqrt_mul hx.1.le _
    _ ≤ √x * Y ^ a := by
        gcongr
        rw [Real.sqrt_le_left (by linarith)]
        nlinarith

theorem const {c : ℝ} (hY : 4 ≤ Y) (hc : 0 < c) (h : 1 ≤ c * 4 ^ a) : LoBd Y a c :=
  ⟨hc, h.trans (by gcongr)⟩

theorem inv (hx : HiBd Y a x) : LoBd Y a x⁻¹ :=
  ⟨inv_pos.mpr hx.1, by rw [inv_mul_eq_div, le_div_iff₀ hx.1]; linarith [hx.2]⟩

end LoBd

namespace HiBd

variable {Y x y : ℝ} {a b : ℕ}

theorem mul (hx : HiBd Y a x) (hy : HiBd Y b y) : HiBd Y (a + b) (x * y) :=
  ⟨mul_pos hx.1 hy.1, by
    rw [pow_add]; exact mul_le_mul hx.2 hy.2 hy.1.le (by linarith [hx.1, hx.2])⟩

theorem inv (hx : LoBd Y a x) : HiBd Y a x⁻¹ :=
  ⟨inv_pos.mpr hx.1, by rw [inv_le_iff_one_le_mul₀ hx.1, mul_comm]; exact hx.2⟩

theorem div (hx : HiBd Y a x) (hy : LoBd Y b y) : HiBd Y (a + b) (x / y) := by
  rw [div_eq_mul_inv]; exact hx.mul (inv hy)

theorem pow (hx : HiBd Y a x) (m : ℕ) : HiBd Y (a * m) (x ^ m) :=
  ⟨pow_pos hx.1 m, by rw [pow_mul]; exact pow_le_pow_left₀ hx.1.le hx.2 m⟩

theorem mono (hY : 1 ≤ Y) (hx : HiBd Y a x) (hab : a ≤ b) : HiBd Y b x :=
  ⟨hx.1, hx.2.trans (pow_le_pow_right₀ hY hab)⟩

theorem of_le (hy : HiBd Y a y) (hx : 0 < x) (hxy : x ≤ y) : HiBd Y a x :=
  ⟨hx, hxy.trans hy.2⟩

theorem add (hY : 2 ≤ Y) (hx : HiBd Y a x) (hy : HiBd Y a y) : HiBd Y (a + 1) (x + y) :=
  ⟨add_pos hx.1 hy.1, by
    rw [pow_succ]
    have : 0 ≤ Y ^ a := hx.1.le.trans hx.2
    nlinarith [hx.2, hy.2]⟩

theorem sqrt (hY : 1 ≤ Y) (hx : HiBd Y a x) : HiBd Y a (√x) := by
  refine ⟨Real.sqrt_pos.mpr hx.1, ?_⟩
  have hYa : 1 ≤ Y ^ a := one_le_pow₀ hY
  rw [Real.sqrt_le_left (by linarith)]
  nlinarith [hx.2]

theorem const {c : ℝ} (hY : 4 ≤ Y) (hc : 0 < c) (h : c ≤ 4 ^ a) : HiBd Y a c :=
  ⟨hc, h.trans (by gcongr)⟩

end HiBd

section Bits

variable {n k : ℕ} {B Γ S δ φ Y : ℝ}

/-- The cap $F$ is at most $Y^{12}$ when $\omega/\Sigma \ge Y^{-8}$. -/
theorem hiBd_shqrCap (hY4 : 4 ≤ Y) (hS : 0 < S) (hω0 : 0 < shqrOmega n B Γ δ)
    (hωS : shqrOmega n B Γ δ ≤ S) (hrr : LoBd Y 8 (shqrOmega n B Γ δ / S)) :
    HiBd Y 12 (shqrCap n B Γ S δ : ℝ) := by
  have hY2 : 2 ≤ Y := by linarith
  set ω := shqrOmega n B Γ δ
  have h4 : 1 ≤ 4 * S / ω := by rw [le_div_iff₀ hω0]; linarith
  have hc : 0.1984 ≤ log (1 / shqrContraction) := by
    have := one_sub_inv_le_log_of_pos (x := 1 / shqrContraction)
      (by unfold shqrContraction; norm_num)
    unfold shqrContraction at this ⊢; norm_num at this ⊢; linarith
  have hl0 : 0 ≤ log (4 * S / ω) := log_nonneg h4
  have hl : log (4 * S / ω) ≤ 4 * S / ω := by
    linarith [log_le_sub_one_of_pos (by linarith : 0 < 4 * S / ω)]
  have hx0 : 0 ≤ log (4 * S / ω) / log (1 / shqrContraction) := div_nonneg hl0 (by linarith)
  have hx : log (4 * S / ω) / log (1 / shqrContraction) ≤ 6 * (4 * (ω / S)⁻¹) := by
    rw [div_le_iff₀ (by linarith), inv_div]
    have : 0 ≤ S / ω := by positivity
    calc log (4 * S / ω) ≤ 4 * S / ω := hl
      _ ≤ 6 * (4 * (S / ω)) * 0.1984 := by rw [mul_div_assoc]; linarith
      _ ≤ 6 * (4 * (S / ω)) * log (1 / shqrContraction) := by gcongr
  have hcap : (shqrCap n B Γ S δ : ℝ) =
      (⌈log (4 * S / ω) / log (1 / shqrContraction)⌉₊ : ℝ) + 1 := by
    rw [shqrCap, Nat.cast_add, Nat.cast_one]
  have hFle : (shqrCap n B Γ S δ : ℝ) ≤ 6 * (4 * (ω / S)⁻¹) + 2 := by
    rw [hcap]
    have := Nat.ceil_lt_add_one hx0
    linarith
  have h9 : HiBd Y 11 (6 * (4 * (ω / S)⁻¹)) :=
    (HiBd.const hY4 (by norm_num) (by norm_num : (6 : ℝ) ≤ 4 ^ 2)).mul
      ((HiBd.const hY4 (by norm_num) (by norm_num : (4 : ℝ) ≤ 4 ^ 1)).mul (HiBd.inv hrr))
  have hF1 : (0 : ℝ) < shqrCap n B Γ S δ := by
    have := one_le_shqrCap (n := n) (B := B) (Γ := Γ) (S := S) (δ := δ)
    exact_mod_cast this
  exact (h9.add hY2 (HiBd.const hY4 (by norm_num) (by norm_num))).of_le hF1 hFle

/-- Regularize's window: $\eta/\Sigma \ge Y^{-49}$. -/
theorem loBd_shqrEta_div (hY4 : 4 ≤ Y) (hS : 0 < S) (hk : 0 < k)
    (hrr : LoBd Y 8 (shqrOmega n B Γ δ / S)) (hφu : LoBd Y 16 (shqrSmallEigFailure n B Γ S δ φ))
    (hkY : HiBd Y 9 (k : ℝ)) : LoBd Y 49 (shqrEta n k B Γ S δ φ / S) := by
  have hY1 : 1 ≤ Y := by linarith
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have e : shqrEta n k B Γ S δ φ / S = (shqrOmega n B Γ δ / S) ^ 2 / 32320 *
      √(shqrSmallEigFailure n B Γ S δ φ / k) := by
    simp only [shqrEta, shqrRadius, shqrRegularizeFailure]
    rw [show 2 * shqrSmallEigFailure n B Γ S δ φ / (2 * k) = shqrSmallEigFailure n B Γ S δ φ / k
      by field_simp]
    field_simp
    ring
  rw [e]
  exact ((hrr.pow 2).div (HiBd.const hY4 (by norm_num) (by norm_num : (32320 : ℝ) ≤ 4 ^ 8))).mul
    ((hφu.div hkY).sqrt hY1)

/-- Sh's separation: $d/\Sigma \ge Y^{-50}$. -/
theorem loBd_shqrDist_div (hY4 : 4 ≤ Y) (hS : 0 < S)
    (hη : LoBd Y 49 (shqrEta n k B Γ S δ φ / S)) (hε : 1 / 100 ≤ shqrEps k (4 * B))
    (hrl : 1 ≤ shqrRadiusLo k (4 * B)) (hrr : LoBd Y 8 (shqrOmega n B Γ δ / S))
    (hφu : LoBd Y 16 (shqrSmallEigFailure n B Γ S δ φ)) (hNY : HiBd Y 1 ((n : ℝ) + 1)) :
    LoBd Y 50 (shqrDist n k B Γ S δ φ / S) := by
  have hY1 : 1 ≤ Y := by linarith
  have e : shqrDist n k B Γ S δ φ / S = min (shqrEta n k B Γ S δ φ / S / 2)
      (shqrEps k (4 * B) * shqrRadiusLo k (4 * B) * (shqrOmega n B Γ δ / S) *
        √(shqrSmallEigFailure n B Γ S δ φ / (11 * ((n : ℝ) + 1))) / 4) := by
    rw [shqrDist, ← min_div_div_right hS.le]
    push_cast
    congr 1 <;> ring
  rw [e]
  have hεY : LoBd Y 4 (shqrEps k (4 * B)) :=
    (LoBd.const hY4 (by norm_num) (by norm_num)).of_le hε
  have hrlY : LoBd Y 0 (shqrRadiusLo k (4 * B)) := ⟨by linarith, by simpa using hrl⟩
  have h2 := (((hεY.mul hrlY).mul hrr).mul ((hφu.div ((HiBd.const hY4 (by norm_num)
    (by norm_num : (11 : ℝ) ≤ 4 ^ 2)).mul hNY)).sqrt hY1)).div
      (HiBd.const hY4 (by norm_num) (by norm_num : (4 : ℝ) ≤ 4 ^ 1))
  exact (hη.div (HiBd.const hY4 (by norm_num) (by norm_num : (2 : ℝ) ≤ 4 ^ 1))).min
    (h2.mono hY1 (by norm_num))

/-- Regularize's precision terms are at least $Y^{-(53k + 40)}$. -/
theorem loBd_uShQRRegularize (hY4 : 4 ≤ Y) (hS : 0 < S) (hk : 1 ≤ k)
    (hrr : LoBd Y 8 (shqrOmega n B Γ δ / S)) (hη : LoBd Y 49 (shqrEta n k B Γ S δ φ / S))
    (hθ : 1 ≤ shqrTheta k (4 * B)) (hkY : HiBd Y 9 (k : ℝ)) (hNY : HiBd Y 1 ((n : ℝ) + 1))
    (hBY : HiBd Y 1 B) : LoBd Y (53 * k + 40) (uShQRRegularize n k B Γ S δ φ) := by
  have hY1 : 1 ≤ Y := by linarith
  have hS0 : S ≠ 0 := hS.ne'
  unfold uShQRRegularize
  simp only [Nat.cast_add, Nat.cast_one]
  set ω := shqrOmega n B Γ δ
  set η := shqrEta n k B Γ S δ φ
  set θ := shqrTheta k (4 * B)
  set N : ℝ := (n : ℝ) + 1
  have c4 : HiBd Y 1 (4 : ℝ) := HiBd.const hY4 (by norm_num) (by norm_num)
  have c2 : HiBd Y 1 (2 : ℝ) := HiBd.const hY4 (by norm_num) (by norm_num)
  have c300 : HiBd Y 5 (300 : ℝ) := HiBd.const hY4 (by norm_num) (by norm_num)
  have cc : HiBd Y 3 (4 * (2 + 2 * 1.1) : ℝ) := HiBd.const hY4 (by norm_num) (by norm_num)
  have h1 : LoBd Y (53 * k + 40) (ω ^ 2 / (16160 * (4 * S) ^ 2)) := by
    rw [show ω ^ 2 / (16160 * (4 * S) ^ 2) = (ω / S) ^ 2 / 258560 by field_simp; ring]
    refine ((hrr.pow 2).div (HiBd.const hY4 (by norm_num) (by norm_num : (258560 : ℝ) ≤ 4 ^ 9))
      ).mono hY1 (by omega)
  have h2 : LoBd Y (53 * k + 40) (η / (8 * (4 * S))) := by
    rw [show η / (8 * (4 * S)) = (η / S) / 32 by field_simp; ring]
    exact (hη.div (HiBd.const hY4 (by norm_num) (by norm_num : (32 : ℝ) ≤ 4 ^ 3))).mono hY1
      (by omega)
  have h3 : LoBd Y (53 * k + 40) ((θ * ω) ^ k /
      (30000 * ↑k * (N * √N) * ((2 + 2 * 1.1) * (4 * S)) ^ k)) := by
    rw [show (θ * ω) ^ k / (30000 * ↑k * (N * √N) * ((2 + 2 * 1.1) * (4 * S)) ^ k) =
        (θ * (ω / S)) ^ k / (30000 * ↑k * (N * √N) * (4 * (2 + 2 * 1.1)) ^ k) by
      rw [show θ * ω = θ * (ω / S) * S by field_simp,
        show (2 + 2 * 1.1) * (4 * S) = 4 * (2 + 2 * 1.1) * S by ring, mul_pow, mul_pow]
      field_simp
      ring]
    have hθr : LoBd Y 8 (θ * (ω / S)) := hrr.of_le (le_mul_of_one_le_left hrr.1.le hθ)
    exact ((hθr.pow k).div ((((HiBd.const hY4 (by norm_num)
      (by norm_num : (30000 : ℝ) ≤ 4 ^ 8)).mul hkY).mul (hNY.mul (hNY.sqrt hY1))).mul
        (cc.pow k))).mono hY1 (by omega)
  have h4 : LoBd Y (53 * k + 40) ((16 * (4 * B))⁻¹ * (η / 2 / ((2 + 2 * 1.1) * (4 * S))) ^ k /
      (300 * N ^ 2)) := by
    rw [show η / 2 / ((2 + 2 * 1.1) * (4 * S)) = η / S / 2 / (4 * (2 + 2 * 1.1)) by
      field_simp]
    exact (((LoBd.inv ((HiBd.const hY4 (by norm_num) (by norm_num : (16 : ℝ) ≤ 4 ^ 2)).mul
      (c4.mul hBY))).mul (((hη.div c2).div cc).pow k)).div (c300.mul (hNY.pow 2))).mono hY1
        (by omega)
  have h5 : LoBd Y (53 * k + 40) (ω / 2 / ((66 + 2 * 1.1) * (4 * B) * (4 * S) *
      ((2 + 2 * 1.1) * (4 * S) / (η / 2)) ^ k * √N * (300 * N ^ 2))) := by
    rw [show (2 + 2 * 1.1) * (4 * S) / (η / 2) = 4 * (2 + 2 * 1.1) / (η / S / 2) by
      field_simp]
    rw [show ω / 2 / ((66 + 2 * 1.1) * (4 * B) * (4 * S) *
      (4 * (2 + 2 * 1.1) / (η / S / 2)) ^ k * √N * (300 * N ^ 2)) =
        ω / S / 2 / ((66 + 2 * 1.1) * (4 * B) * 4 *
      (4 * (2 + 2 * 1.1) / (η / S / 2)) ^ k * √N * (300 * N ^ 2)) by field_simp]
    exact ((hrr.div c2).div (((((HiBd.const hY4 (by norm_num)
      (by norm_num : (66 + 2 * 1.1 : ℝ) ≤ 4 ^ 4)).mul (c4.mul hBY)).mul c4).mul
        ((cc.div (hη.div c2)).pow k)).mul (hNY.sqrt hY1) |>.mul (c300.mul (hNY.pow 2)))).mono
          hY1 (by omega)
  exact h1.min (h2.min (h3.min (h4.min h5)))

/-- Sh's precision terms are at least $Y^{-(53k + 40)}$. -/
theorem loBd_uShQRSh (hY4 : 4 ≤ Y) (hS : 0 < S) (hk : 1 ≤ k)
    (hrr : LoBd Y 8 (shqrOmega n B Γ δ / S)) (hd : LoBd Y 50 (shqrDist n k B Γ S δ φ / S))
    (hε : 1 / 100 ≤ shqrEps k (4 * B)) (hrl : 1 ≤ shqrRadiusLo k (4 * B))
    (hrh0 : 0 < shqrRadiusHi k (4 * B)) (hrh : shqrRadiusHi k (4 * B) ≤ 3)
    (hC0 : 0 < shqrC k (4 * B)) (hC : shqrC k (4 * B) ≤ 7)
    (hφu : LoBd Y 16 (shqrSmallEigFailure n B Γ S δ φ)) (hNY : HiBd Y 1 ((n : ℝ) + 1))
    (hBY : HiBd Y 1 B) : LoBd Y (53 * k + 40) (uShQRSh n k B Γ S δ φ) := by
  have hY1 : 1 ≤ Y := by linarith
  have hS0 : S ≠ 0 := hS.ne'
  unfold uShQRSh
  simp only [Nat.cast_add, Nat.cast_one]
  set ω := shqrOmega n B Γ δ
  set d := shqrDist n k B Γ S δ φ
  set ε := shqrEps k (4 * B)
  set rl := shqrRadiusLo k (4 * B)
  set rh := shqrRadiusHi k (4 * B)
  set C := shqrC k (4 * B)
  set φu := shqrSmallEigFailure n B Γ S δ φ
  set N : ℝ := (n : ℝ) + 1
  have c4 : HiBd Y 1 (4 : ℝ) := HiBd.const hY4 (by norm_num) (by norm_num)
  have c300 : HiBd Y 5 (300 : ℝ) := HiBd.const hY4 (by norm_num) (by norm_num)
  have cc : HiBd Y 3 (4 * (2 + 2 * C)) := HiBd.const hY4 (by positivity) (by linarith)
  have hεY : LoBd Y 4 ε := (LoBd.const hY4 (by norm_num) (by norm_num)).of_le hε
  have hrlY : LoBd Y 0 rl := ⟨by linarith, by simpa using hrl⟩
  have hden : HiBd Y 4 (6 * (1.1 * 4 + 3 * rh * 4)) :=
    HiBd.const hY4 (by positivity) (by nlinarith)
  have h1 : LoBd Y (53 * k + 40)
      ((8004 * (4 * B))⁻¹ * (d / ((2 + 2 * C) * (4 * S))) ^ k / (300 * N ^ 2)) := by
    rw [show d / ((2 + 2 * C) * (4 * S)) = d / S / (4 * (2 + 2 * C)) by field_simp]
    exact (((LoBd.inv ((HiBd.const hY4 (by norm_num) (by norm_num : (8004 : ℝ) ≤ 4 ^ 7)).mul
      (c4.mul hBY))).mul ((hd.div cc).pow k)).div (c300.mul (hNY.pow 2))).mono hY1 (by omega)
  have h2 : LoBd Y (53 * k + 40) (1e-3 * ω / ((66 + 2 * C) * (4 * B) * (4 * S) *
      ((2 + 2 * C) * (4 * S) / d) ^ k * √N * (300 * N ^ 2))) := by
    rw [show (2 + 2 * C) * (4 * S) / d = 4 * (2 + 2 * C) / (d / S) by field_simp]
    rw [show 1e-3 * ω / ((66 + 2 * C) * (4 * B) * (4 * S) *
      (4 * (2 + 2 * C) / (d / S)) ^ k * √N * (300 * N ^ 2)) =
        1e-3 * (ω / S) / ((66 + 2 * C) * (4 * B) * 4 *
      (4 * (2 + 2 * C) / (d / S)) ^ k * √N * (300 * N ^ 2)) by field_simp]
    exact (((LoBd.const hY4 (by norm_num) (by norm_num : (1 : ℝ) ≤ 1e-3 * 4 ^ 5)).mul hrr).div
      (((((HiBd.const hY4 (by positivity) (by linarith : 66 + 2 * C ≤ 4 ^ 4)).mul
        (c4.mul hBY)).mul c4).mul ((cc.div hd).pow k)).mul (hNY.sqrt hY1) |>.mul
          (c300.mul (hNY.pow 2)))).mono hY1 (by omega)
  have h3 : LoBd Y (53 * k + 40)
      (5e-3 * ε * rl * ω / (6 * (1.1 * (4 * S) + 3 * rh * (4 * S)))) := by
    rw [show 5e-3 * ε * rl * ω / (6 * (1.1 * (4 * S) + 3 * rh * (4 * S))) =
      5e-3 * ε * rl * (ω / S) / (6 * (1.1 * 4 + 3 * rh * 4)) by field_simp]
    exact (((((LoBd.const hY4 (by norm_num) (by norm_num : (1 : ℝ) ≤ 5e-3 * 4 ^ 4)).mul
      hεY).mul hrlY).mul hrr).div hden).mono hY1 (by omega)
  have h4 : LoBd Y (53 * k + 40)
      (ε * rl * ω * √(φu / (11 * N)) / 8 / (6 * (1.1 * (4 * S) + 3 * rh * (4 * S)))) := by
    rw [show ε * rl * ω * √(φu / (11 * N)) / 8 / (6 * (1.1 * (4 * S) + 3 * rh * (4 * S))) =
      ε * rl * (ω / S) * √(φu / (11 * N)) / 8 / (6 * (1.1 * 4 + 3 * rh * 4)) by
        field_simp]
    exact (((((hεY.mul hrlY).mul hrr).mul ((hφu.div ((HiBd.const hY4 (by norm_num)
      (by norm_num : (11 : ℝ) ≤ 4 ^ 2)).mul hNY)).sqrt hY1)).div
        (HiBd.const hY4 (by norm_num) (by norm_num : (8 : ℝ) ≤ 4 ^ 2))).div hden).mono hY1
          (by omega)
  exact h1.min (h2.min (h3.min h4))

/-- The loop's precision terms are at least $Y^{-(53k + 40)}$. -/
theorem loBd_uShQRLoop (hY4 : 4 ≤ Y) (hS : 0 < S) (hk : 1 ≤ k)
    (hbs : LoBd Y 5 (shqrBudget n B Γ δ / S)) (hF : HiBd Y 12 (shqrCap n B Γ S δ : ℝ))
    (hC0 : 0 < shqrC k (4 * B)) (hC : shqrC k (4 * B) ≤ 7) (hkY : HiBd Y 9 (k : ℝ))
    (hNY : HiBd Y 1 ((n : ℝ) + 1)) : LoBd Y (53 * k + 40) (uShQRLoop n k B Γ S δ) := by
  have hY1 : 1 ≤ Y := by linarith
  have hS0 : S ≠ 0 := hS.ne'
  unfold uShQRLoop
  set C := shqrC k (4 * B)
  set N : ℝ := (n : ℝ) + 1
  have hkN : HiBd Y 17 (2 * k * (300 * N ^ 2)) :=
    ((HiBd.const hY4 (by norm_num) (by norm_num : (2 : ℝ) ≤ 4 ^ 1)).mul hkY).mul
      ((HiBd.const hY4 (by norm_num) (by norm_num : (300 : ℝ) ≤ 4 ^ 5)).mul (hNY.pow 2))
  have h1 : LoBd Y (53 * k + 40) (1 / (2 * k * (300 * N ^ 2))) := by
    rw [one_div]; exact (LoBd.inv hkN).mono hY1 (by omega)
  have h2 : LoBd Y (53 * k + 40) (shqrBudget n B Γ δ / (6 * N) /
      (shqrCap n B Γ S δ * ((3.1 + C) * (4 * S)) * (2 * k * (300 * N ^ 2)))) := by
    rw [show shqrBudget n B Γ δ / (6 * N) /
      (shqrCap n B Γ S δ * ((3.1 + C) * (4 * S)) * (2 * k * (300 * N ^ 2))) =
        shqrBudget n B Γ δ / S / (6 * N) /
      (shqrCap n B Γ S δ * ((3.1 + C) * 4) * (2 * k * (300 * N ^ 2))) by field_simp]
    exact ((hbs.div ((HiBd.const hY4 (by norm_num) (by norm_num : (6 : ℝ) ≤ 4 ^ 2)).mul hNY)).div
      ((hF.mul (HiBd.const hY4 (by positivity) (by linarith : (3.1 + C) * 4 ≤ 4 ^ 3))).mul
        hkN)).mono hY1 (by omega)
  exact h1.min h2

/-- The counting terms are at least $Y^{-(53k + 40)}$. -/
theorem loBd_uShQRBasic (hY4 : 4 ≤ Y) (hkY : HiBd Y 9 (k : ℝ))
    (hNY : HiBd Y 1 ((n : ℝ) + 1)) : LoBd Y (53 * k + 40) (uShQRBasic n k) := by
  have hY1 : 1 ≤ Y := by linarith
  have hY2 : 2 ≤ Y := by linarith
  unfold uShQRBasic
  simp only [Nat.cast_add, Nat.cast_one]
  refine LoBd.min ((LoBd.const hY4 (by norm_num) (by norm_num : (1 : ℝ) ≤ 1 / 10 * 4 ^ 2)).mono
    hY1 (by omega)) ?_
  rw [one_div]
  exact (LoBd.inv ((HiBd.const hY4 (by norm_num) (by norm_num : (100000 : ℝ) ≤ 4 ^ 9)).mul
    (((hNY.mono hY1 (by norm_num : 1 ≤ 9)).add hY2 hkY).pow 2))).mono hY1 (by omega)

/-- The scale-invariant argument $Y = 4(n + 1)B\Sigma^2/(\delta\min(\Gamma, \Sigma)\varphi)$ is at
least $4$ and dominates $n + 1$, $B$, $\Sigma/\delta$, $\Sigma/\min(\Gamma, \Sigma)$ and
$1/\varphi$, for $B \ge 1$, $\Gamma > 0$, $0 < \delta \le \Sigma$ and $0 < \varphi \le 1$. -/
theorem shqrArg_bounds (hB : 1 ≤ B) (hΓ : 0 < Γ) (hδ : 0 < δ) (hδS : δ ≤ S) (hφ : 0 < φ)
    (hφ1 : φ ≤ 1) (hY : Y = 4 * (n + 1) * B * S ^ 2 / (δ * min Γ S * φ)) :
    4 ≤ Y ∧ HiBd Y 1 ((n : ℝ) + 1) ∧ HiBd Y 1 B ∧ LoBd Y 1 (δ / S) ∧ LoBd Y 1 (min Γ S / S) ∧
      LoBd Y 1 φ := by
  have hS : 0 < S := hδ.trans_le hδS
  have hB0 : 0 < B := by linarith
  set N : ℝ := (n : ℝ) + 1 with hN
  have hN1 : 1 ≤ N := by rw [hN]; linarith [n.cast_nonneg (α := ℝ)]
  set m := min Γ S with hm
  have hm0 : 0 < m := lt_min hΓ hS
  have hmS : m ≤ S := min_le_right _ _
  have hmΓ : m ≤ Γ := min_le_left _ _
  have hP0 : 0 < δ * m * φ := by positivity
  have hdm : δ * m ≤ S ^ 2 := by rw [sq]; exact mul_le_mul hδS hmS hm0.le hS.le
  have hP : δ * m * φ ≤ S ^ 2 := by nlinarith
  have hNB : 1 ≤ N * B := one_le_mul_of_one_le_of_one_le hN1 hB
  have hY4 : 4 ≤ Y := by
    rw [hY, le_div_iff₀ hP0]; nlinarith
  have hY1 : 1 ≤ Y := by linarith
  have hS2 : 0 ≤ S ^ 2 := sq_nonneg S
  have hNY : HiBd Y 1 N := ⟨by linarith, by
    rw [pow_one, hY, le_div_iff₀ hP0]
    have h1 : N * (δ * m * φ) ≤ N * S ^ 2 := mul_le_mul_of_nonneg_left hP (by linarith)
    have h2 := mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ N) hS2) (by linarith : 0 ≤ 4 * B - 1)
    nlinarith⟩
  have hBY : HiBd Y 1 B := ⟨hB0, by
    rw [pow_one, hY, le_div_iff₀ hP0]
    have h1 : B * (δ * m * φ) ≤ B * S ^ 2 := mul_le_mul_of_nonneg_left hP hB0.le
    have h2 := mul_nonneg (mul_nonneg hB0.le hS2) (by linarith : 0 ≤ 4 * N - 1)
    nlinarith⟩
  have hδY : LoBd Y 1 (δ / S) := ⟨by positivity, by
    rw [pow_one, hY, div_mul_div_comm, le_div_iff₀ (by positivity), one_mul]
    have hmφ : m * φ ≤ S := (mul_le_of_le_one_right hm0.le hφ1).trans hmS
    calc S * (δ * m * φ) = S * δ * (m * φ) := by ring
      _ ≤ S * δ * S := by gcongr
      _ = δ * S ^ 2 * 1 := by ring
      _ ≤ δ * S ^ 2 * (4 * N * B) := by gcongr; linarith
      _ = δ * (4 * N * B * S ^ 2) := by ring⟩
  have hmY : LoBd Y 1 (m / S) := ⟨by positivity, by
    rw [pow_one, hY, div_mul_div_comm, le_div_iff₀ (by positivity), one_mul]
    have hδφ : δ * φ ≤ S := (mul_le_of_le_one_right hδ.le hφ1).trans hδS
    calc S * (δ * m * φ) = S * m * (δ * φ) := by ring
      _ ≤ S * m * S := by gcongr
      _ = m * S ^ 2 * 1 := by ring
      _ ≤ m * S ^ 2 * (4 * N * B) := by gcongr; linarith
      _ = m * (4 * N * B * S ^ 2) := by ring⟩
  have hφY : LoBd Y 1 φ := ⟨hφ, by
    rw [pow_one, hY, mul_div_assoc', le_div_iff₀ hP0, one_mul]
    calc δ * m * φ = φ * (δ * m) := by ring
      _ ≤ φ * S ^ 2 * 1 := by rw [mul_one]; gcongr
      _ ≤ φ * S ^ 2 * (4 * N * B) := by gcongr; linarith
      _ = φ * (4 * N * B * S ^ 2) := by ring⟩
  exact ⟨hY4, hNY, hBY, hδY, hmY, hφY⟩

/-- The precision threshold is polynomial in the scale-invariant argument: for $B \ge 1$,
$\Gamma > 0$, $0 < \delta \le \Sigma$, $0 < \varphi \le 1$ and $k$ the degree of (eqn:setk) at
$4B$, the argument $Y = 4(n + 1)B\Sigma^2/(\delta\min(\Gamma, \Sigma)\varphi)$ is at least $4$
and $\boldsymbol{u}_{\mathrm{ShQR}} \ge Y^{-(53k + 40)}$. -/
theorem one_le_uShQR_mul (hB : 1 ≤ B) (hΓ : 0 < Γ) (hδ : 0 < δ) (hδS : δ ≤ S) (hφ : 0 < φ)
    (hφ1 : φ ≤ 1) (hk : k = shqrDegree (4 * B)) :
    4 ≤ 4 * (n + 1) * B * S ^ 2 / (δ * min Γ S * φ) ∧
    1 ≤ uShQR n k B Γ S δ φ * (4 * (n + 1) * B * S ^ 2 / (δ * min Γ S * φ)) ^ (53 * k + 40) := by
  have hS : 0 < S := hδ.trans_le hδS
  have hB0 : 0 < B := by linarith
  have hB4 : 1 ≤ 4 * B := by linarith
  have hk4 : (4 : ℝ) ≤ k := hk ▸ (shqrDegree_facts hB4).1
  have hk1 : 1 ≤ k := by exact_mod_cast (show (1 : ℝ) ≤ k by linarith)
  have hkB : (k : ℝ) ≤ 512 * (4 * B) ^ 2 := hk ▸ shqrDegree_le hB4
  have hε : 1 / 100 ≤ shqrEps k (4 * B) := hk ▸ shqrEps_ge hB4
  have hC : shqrC k (4 * B) ≤ 7 := hk ▸ shqrC_le hB4
  have hC0 := shqrC_pos k (by linarith : (0 : ℝ) < 4 * B)
  have hθ1 := one_le_shqrTheta k hB4
  have hα1 := one_le_shqrAlpha k hB4
  have hrh0 := shqrRadiusHi_pos k (by linarith : (0 : ℝ) < 4 * B)
  have hrl1 : 1 ≤ shqrRadiusLo k (4 * B) := by
    unfold shqrRadiusLo
    have h1 : 1 ≤ (1.998 : ℝ) ^ ((k : ℝ)⁻¹) := one_le_rpow (by norm_num) (by positivity)
    have h2 : 1 ≤ (4 * B) ^ ((k : ℝ)⁻¹) := one_le_rpow hB4 (by positivity)
    exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le h1 hθ1) hα1) h2
  have hrh : shqrRadiusHi k (4 * B) ≤ 3 := by
    unfold shqrC at hC; linarith
  have hωS : shqrOmega n B Γ δ ≤ S := shqrOmega_le_normBound hB hΓ hδ hδS
  have hω0 : 0 < shqrOmega n B Γ δ := shqrOmega_pos hB hΓ hδ
  obtain ⟨hY4, hNY, hBY, hδY, hmY, hφY⟩ := shqrArg_bounds (n := n) hB hΓ hδ hδS hφ hφ1 rfl
  set N : ℝ := (n : ℝ) + 1 with hN
  set Y := 4 * N * B * S ^ 2 / (δ * min Γ S * φ) with hY
  refine ⟨hY4, ?_⟩
  have hY1 : 1 ≤ Y := by linarith
  set m := min Γ S with hm
  have hmΓ : m ≤ Γ := min_le_left _ _
  have hkY : HiBd Y 9 (k : ℝ) :=
    ((HiBd.const hY4 (by norm_num) (by norm_num : (8192 : ℝ) ≤ 4 ^ 7)).mul
      (hBY.pow 2)).of_le (by linarith) (by nlinarith)
  have hbs : LoBd Y 5 (shqrBudget n B Γ δ / S) := by
    have h16 : HiBd Y 4 (16 * N * B) :=
      ((HiBd.const hY4 (by norm_num) (by norm_num : (16 : ℝ) ≤ 4 ^ 2)).mul hNY).mul hBY
    refine ((hδY.mono hY1 (by norm_num)).min (hmY.div h16)).of_le ?_
    rw [le_div_iff₀ hS]
    unfold shqrBudget
    refine le_min ?_ ?_
    · calc min (δ / S) (m / S / (16 * N * B)) * S ≤ δ / S * S := by gcongr; exact min_le_left _ _
        _ = δ := by field_simp
    · calc min (δ / S) (m / S / (16 * N * B)) * S ≤ m / S / (16 * N * B) * S := by
            gcongr; exact min_le_right _ _
        _ = m / (16 * N * B) := by field_simp
        _ ≤ Γ / (16 * N * B) := by gcongr
  have hrr : LoBd Y 8 (shqrOmega n B Γ δ / S) := by
    have e : shqrOmega n B Γ δ / S = shqrBudget n B Γ δ / S / (12 * N) := by
      simp only [shqrOmega, hN]; ring
    rw [e]
    exact hbs.div ((HiBd.const hY4 (by norm_num) (by norm_num : (12 : ℝ) ≤ 4 ^ 2)).mul hNY)
  have hF := hiBd_shqrCap hY4 hS hω0 hωS hrr
  have hφu : LoBd Y 16 (shqrSmallEigFailure n B Γ S δ φ) :=
    hφY.div (((HiBd.const hY4 (by norm_num) (by norm_num : (12 : ℝ) ≤ 4 ^ 2)).mul hF).mul hNY)
  have hη := loBd_shqrEta_div hY4 hS (by omega) hrr hφu hkY
  have hd := loBd_shqrDist_div hY4 hS hη hε hrl1 hrr hφu hNY
  have hu : LoBd Y (53 * k + 40) (uShQR n k B Γ S δ φ) :=
    (loBd_uShQRBasic hY4 hkY hNY).min ((loBd_uShQRRegularize hY4 hS hk1 hrr hη hθ1 hkY hNY hBY).min
      ((loBd_uShQRSh hY4 hS hk1 hrr hd hε hrl1 hrh0 hrh hC0 hC hφu hNY hBY).min
        (loBd_uShQRLoop hY4 hS hk1 hbs hF hC0 hC hkY hNY)))
  exact hu.2

end Bits

end NLAlib.ShiftedQR
