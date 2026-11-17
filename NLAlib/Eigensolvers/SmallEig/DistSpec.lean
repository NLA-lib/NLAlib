/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.ShiftedQR.RoundedFindTermination
public import NLAlib.ForMathlib.LinearAlgebra.Matrix.NonsingularInverse
public import NLAlib.Eigensolvers.SmallEig.Parameters
public import NLAlib.Matrix.FinitePrecision.RootsRounded
public import NLAlib.Matrix.QRIteration.InverseIteration

/-!
# `DistSpec`: the distance from a shift to the spectrum

`DistSpec` ([BanksGarzaVargasSrivastava2025, §3.1]) estimates the distance from a shift $s$ to the
spectrum of an upper Hessenberg $\mathbf{H}$: $m = 2^q$ rounded QR steps with the shift $s$, the
product of the moduli of the last diagonal entries of their triangular factors
(`NLAlib.ShiftedQR.comptauHalf` with the one shift repeated $m$ times), approximately
$\tau^m = \|\mathbf{e}_n^{\mathsf{T}}(\mathbf{H} - s)^{-m}\|^{-1}$, and $q$ rounded square roots.
With $m$ large for the condition $\kappa$ and the weight $p$
(`NLAlib.SmallEig.distSpecDegree_spec`) the estimate is within $10\%$ of the distance.

## Main definitions

* `NLAlib.SmallEig.distSpec`: the program `[N, m, q] (H, S) → (Tau)`.

## Main results

* `NLAlib.SmallEig.abs_distSpecWord_sub_le`: the rounding of the roots.
* `NLAlib.SmallEig.distSpec_root_bounds`: the roots of an estimate of a power of a distance.
* `NLAlib.SmallEig.distSpec_writes_word`, `NLAlib.SmallEig.distSpec_accuracy`,
  `NLAlib.SmallEig.distSpec_terminates`.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib.SmallEig

open Ops ShiftedQR

section Program

variable {O Q : Type} [Has ScalarOp O] [Has CmpTst Q]

/-- **`DistSpec`** ([BanksGarzaVargasSrivastava2025, Proposition 3.1], with $m = 2^q$): from the
order-$N$ matrix `H` and the shift pair `S`, `NLAlib.ShiftedQR.comptauHalf` with the shift
repeated $m$ times into `Tau`, then $q$ rounded square roots of `Tau` in place
(`NLAlib.ShiftedQR.squareRoots`). The degree $m$ and its exponent $q$ are dimensions, read by
the caller from cap words. The interface is `[N, m, q] (H, S) → (Tau)`; the copy of the matrix
is scoped.
Algorithm: small-eig -/
def distSpec : Impl O Q := opsImpl% [N, m, q] (H, S) → (Tau) {
  run (comptauHalf (O := O) (Q := Q)).body [N, 1, m] (H, S, Tau);
  run (squareRoots (Op := O) (Tst := Q)).body [q] (Tau, Tau)
}

end Program

/-- **The roots of `DistSpec` keep a $0.11\%$ estimate within $0.2\%$**
([BanksGarzaVargasSrivastava2025, Proposition 3.1], the rounding part): on a machine with the
standard model at $0 \le \boldsymbol{u}$ with $30000(2^q + 1)\boldsymbol{u} \le 1$, for
$\tau \ge 0$ and a word $t$ with $\lvert t - \tau^{2^q}\rvert \le 0.0011\,\tau^{2^q}$, the $q$
rounded square roots of $t$ are within $0.002\,\tau$ of $\tau$. -/
theorem abs_distSpecWord_sub_le {M : Machine ℝ} {u : ℝ} (hM : StdModel u id M) (hu : 0 ≤ u)
    {q : ℕ} (hu' : 30000 * ((2 : ℝ) ^ q + 1) * u ≤ 1) {τ t : ℝ} (hτ : 0 ≤ τ)
    (ht : |t - τ ^ 2 ^ q| ≤ 0.0011 * τ ^ 2 ^ q) :
    |sqrtIter M q t - τ| ≤ 0.002 * τ := by
  have h2q : (1 : ℝ) ≤ 2 ^ q := one_le_pow₀ (by norm_num)
  have hu2 : u ≤ 1 / 60000 := by nlinarith
  have hr := abs_rpow_inv_sub_le_of_abs_sub_pow_le (k := 2 ^ q) (by positivity) hτ
    (by norm_num) (by norm_num) ht
  have ht0 : 0 ≤ t := by nlinarith [(abs_le.mp ht).1, pow_nonneg hτ (2 ^ q)]
  have hs := hM.abs_sqrtIter_sub_le hu (by linarith) q ht0
  push_cast at hr
  have hr' := (abs_le.mp hr).2
  have := abs_sub_le (sqrtIter M q t) (t ^ ((2 : ℝ) ^ q)⁻¹) τ
  nlinarith [mul_nonneg hu hτ]

/-- The polynomial of the one shift $s$, at $\mathbf{H}$, has the inverse powers of
$s\mathbf{I} - \mathbf{H}$ up to sign: the last rows of
$p_{[s]}(\mathbf{H})^{-m}$ and $(s\mathbf{I} - \mathbf{H})^{-m}$ have the same norm. -/
theorem norm_toLp_lastRow_inv_shiftPoly_singleton_pow {n : ℕ}
    (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (s : ℂ) (m : ℕ) :
    ‖WithLp.toLp 2 (((Polynomial.aeval H (shiftPoly [s]))⁻¹ ^ m) (Fin.last n))‖ =
      ‖WithLp.toLp 2 (((s • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) - H)⁻¹ ^ m)
        (Fin.last n))‖ := by
  have he : Polynomial.aeval H (shiftPoly [s]) = -(s • 1 - H) := by
    simp [shiftPoly, Algebra.algebraMap_eq_smul_one]
  rw [he, Matrix.inv_neg, neg_pow]
  rcases neg_one_pow_eq_or (Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) m with h | h
  · rw [h, one_mul]
  · rw [h, neg_one_mul, show ∀ X : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, (-X) (Fin.last n) =
      -X (Fin.last n) from fun _ => rfl, WithLp.toLp_neg, norm_neg]

/-- **The roots of an estimate of the $m$-th power of a distance** (the arithmetic of
[BanksGarzaVargasSrivastava2025, Proposition 3.1] with "$m$ is large enough"): for $\kappa \ge 1$,
$0 < p \le 1$, $m \ge 1$ at least `NLAlib.SmallEig.distSpecDegree` $\kappa$ $p$, $D > 0$ and
$X \ge 0$ with $D^m \le \kappa X$ and $\sqrt p\,X \le \kappa D^m$, every $r$ within $0.002\,\tau_0$
of $\tau_0 = X^{1/m}$ satisfies $0.9\,D \le r \le 1.1\,D$. -/
theorem distSpec_root_bounds {κ p D X r : ℝ} {m : ℕ} (hκ : 1 ≤ κ) (hp : 0 < p) (hp1 : p ≤ 1)
    (hm0 : 0 < m) (hm : distSpecDegree κ p ≤ m) (hD : 0 < D) (hX : 0 ≤ X)
    (hlo : D ^ m ≤ κ * X) (hhi : √p * X ≤ κ * D ^ m)
    (hr : |r - X ^ ((m : ℝ)⁻¹)| ≤ 0.002 * X ^ ((m : ℝ)⁻¹)) :
    0.9 * D ≤ r ∧ r ≤ 1.1 * D := by
  obtain ⟨h1, h2⟩ := distSpecDegree_spec hκ hp hp1 hm0 hm
  have hκ0 : 0 < κ := by linarith
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm0.ne'
  set τ₀ := X ^ ((m : ℝ)⁻¹) with hτ₀
  have hτ0 : 0 ≤ τ₀ := Real.rpow_nonneg hX _
  have hτm : τ₀ ^ m = X := Real.rpow_inv_natCast_pow hX hm0.ne'
  -- `a ^ m` for `a = κ ^ (± 1 / m)` and `p ^ (-1 / (2m))`
  have hpowκ : ∀ e : ℝ, (κ ^ (e * (m : ℝ)⁻¹)) ^ m = κ ^ e := fun e => by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hκ0.le, mul_assoc, inv_mul_cancel₀ hm', mul_one]
  have hlow : D * κ ^ (-(m : ℝ)⁻¹) ≤ τ₀ := by
    refine (pow_le_pow_iff_left₀ (by positivity) hτ0 hm0.ne').mp ?_
    rw [mul_pow, show -(m : ℝ)⁻¹ = -1 * (m : ℝ)⁻¹ by ring, hpowκ, hτm, Real.rpow_neg_one,
      ← div_eq_mul_inv, div_le_iff₀ hκ0]
    linarith
  have hsp : 0 < √p := Real.sqrt_pos.mpr hp
  have hpp : (p ^ (-(2 * (m : ℝ))⁻¹)) ^ m = (√p)⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hp.le, Real.sqrt_eq_rpow, ← Real.rpow_neg hp.le]
    congr 1; field_simp
  have hhigh : τ₀ ≤ D * (κ ^ ((m : ℝ)⁻¹) * p ^ (-(2 * (m : ℝ))⁻¹)) := by
    refine (pow_le_pow_iff_left₀ hτ0 (by positivity) hm0.ne').mp ?_
    rw [mul_pow, mul_pow, show (m : ℝ)⁻¹ = 1 * (m : ℝ)⁻¹ by ring, hpowκ, hpp, hτm,
      Real.rpow_one, ← mul_assoc, le_mul_inv_iff₀ hsp]
    linarith
  have hr' := abs_le.mp hr
  have hκ1 : 0 < κ ^ (-(m : ℝ)⁻¹) := Real.rpow_pos_of_pos hκ0 _
  constructor
  · nlinarith
  · nlinarith

section Theorems

variable {O Q : Type} [Has ScalarOp O] [Has CmpTst Q]

/-- `DistSpec` on any scalar machine: if `NLAlib.ShiftedQR.comptauHalf` meets the comparison
contract of the shift $s$ repeated, $m \ge 1$ (`NLAlib.ShiftedQR.IsHalfTau` for $\mathbf{H}$ of
order $n + 1$ and the list of $2m$ copies of $s$), then from $\mathbf{H}$ at `h`, the pair of $s$ at
`s` and room for the word `tau` (in a buffer of its own), `NLAlib.SmallEig.distSpec` writes only
that word, keeps the tape position, and stores $q$ rounded square roots of a $t$ within
$0.0011$, relatively, of $\|\mathbf{e}_n^{\mathsf{T}}(\mathbf{H} - s\mathbf{I})^{-m}\|^{-1}$. -/
theorem distSpec_writes_word {M : Machine ℝ} {I : Interp O Q ℝ} (hS : IsScalar M I) {n m q : ℕ}
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {s : ℂ} (hm : 0 < m)
    (hT : IsHalfTau H (List.replicate (2 * m) s) (comptauHalf (O := O) (Q := Q)) I)
    {τ : Tape ℝ} {μ : Mem ℝ} {h sp tau : ℕ × ℕ} (hl : μ.Live [h, sp, tau])
    (hH : HoldsMatrix h H μ.store) (hsp : μ.store.readBlock sp.1 sp.2 2 = some [s.re, s.im])
    (htau : tau.2 < μ.store.len tau.1) (hth : tau.1 ≠ h.1) (hts : tau.1 ≠ sp.1) :
    Writes .total I τ (distSpec (O := O) (Q := Q)).body (Env.frame [n + 1, m, q] [h, sp, tau])
      (Store.inBlock tau.1 tau.2 1)
      (fun μ' => μ'.pos = μ.pos ∧ ∃ t : ℝ, μ'.store.get tau.1 tau.2 = some (sqrtIter M q t) ∧
        |t - ‖WithLp.toLp 2 (((s • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) - H)⁻¹ ^ m)
          (Fin.last n))‖⁻¹| ≤ 0.0011 * ‖WithLp.toLp 2
            (((s • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) - H)⁻¹ ^ m) (Fin.last n))‖⁻¹) μ := by
  have h1 : ((List.replicate (2 * m) s).drop 0).take 1 = [s] := by
    obtain ⟨k, hk⟩ : ∃ k, 2 * m = k + 1 := ⟨2 * m - 1, by omega⟩
    rw [hk, List.drop_zero, List.replicate_succ, List.take_succ_cons, List.take_zero]
  have hA := hT 0 1 m (by simp; omega) (by rw [List.length_replicate]; ring) τ μ h sp tau hl hH
    (by rw [h1]; simpa using hsp) htau hth hts
  rw [h1, norm_toLp_lastRow_inv_shiftPoly_singleton_pow] at hA
  unfold distSpec
  refine hA.frame_seq_le rfl rfl hl le_rfl ?_
  rintro μ₁ - ⟨hp₁, t, ht, hb⟩
  refine ((squareRoots_writes_word (τ := τ) (k := q) hS ht).in_frame rfl rfl
    (by simpa [Mem.Live] using Store.lt_length_of_get ht)).mono le_rfl ?_
  rintro μ₂ - ⟨hp₂, hR₂⟩
  exact ⟨hp₂.trans hp₁, t, hR₂, hb⟩

/-- **`DistSpec` is within $10\%$ of the distance to the spectrum**
([BanksGarzaVargasSrivastava2025, Proposition 3.1 and Observation 3.3]): on a scalar machine
with the standard model at $\boldsymbol{u}$ and exact comparisons, let
$\mathbf{H} \ne 0$ of order $n + 1$ be upper Hessenberg,
$\mathbf{H}\mathbf{V} = \mathbf{V}\operatorname{diag}(\mathbf{d})$ with
$\|\mathbf{V}\|_2\|\mathbf{V}^{-1}\|_2 \le \kappa$ and every last-row weight at least $p > 0$, the
shift $s$ in $\mathbb{D}(0, C\|\mathbf{H}\|_2)$ ($C \ge 0$) at distance at least $\eta_1 > 0$ from
every $d_i$, $m = 2^q$ at least `NLAlib.SmallEig.distSpecDegree` $\kappa$ $p$, and
$(n + 1)\boldsymbol{u} \le 1/2500$, $30000(m + 1)\boldsymbol{u} \le 1$,
$300(n + 1)^2\boldsymbol{u} \le (8004\kappa)^{-1}(\eta_1/((2 + 2C)\|\mathbf{H}\|_2))^m$. Then from
$\mathbf{H}$ at `h`, the pair of $s$ at `s` and room for the word `tau`, `NLAlib.SmallEig.distSpec`
writes only that word, keeps the tape position, and stores $\hat\tau$ with
$0.9\,D \le \hat\tau \le 1.1\,D$, $D = \min_i\lvert s - d_i\rvert$. -/
theorem distSpec_accuracy {M : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ} (hS : IsScalar M I)
    (hM : StdModel u id M) (hCmp : IsCmp id I) {n m q : ℕ}
    {H V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {d : Fin (n + 1) → ℂ} {s : ℂ} {κ p C η₁ : ℝ}
    (hH : IsUpperHessenberg H) (hH0 : H ≠ 0) (hV : IsUnit V)
    (hHV : H * V = V * Matrix.diagonal d) (hκ : pseudoConditionNumber V ≤ κ) (hp : 0 < p)
    (hw : ∀ i, p ≤ lastRowWeights V i) (hC : 0 ≤ C) (hs : ‖s‖ ≤ C * specNorm H)
    (hη₁ : 0 < η₁) (hdist : ∀ i, η₁ ≤ ‖d i - s‖) (hmq : m = 2 ^ q)
    (hm : distSpecDegree κ p ≤ m) (hnu : (n + 1 : ℝ) * u ≤ 1 / 2500)
    (hum : 30000 * ((m : ℝ) + 1) * u ≤ 1)
    (hxu : 300 * (n + 1) ^ 2 * u ≤ (8004 * κ)⁻¹ * (η₁ / ((2 + 2 * C) * specNorm H)) ^ m)
    {τ : Tape ℝ} {μ : Mem ℝ} {h sp tau : ℕ × ℕ} (hl : μ.Live [h, sp, tau])
    (hHs : HoldsMatrix h H μ.store) (hsp : μ.store.readBlock sp.1 sp.2 2 = some [s.re, s.im])
    (htau : tau.2 < μ.store.len tau.1) (hth : tau.1 ≠ h.1) (hts : tau.1 ≠ sp.1) :
    Writes .total I τ (distSpec (O := O) (Q := Q)).body (Env.frame [n + 1, m, q] [h, sp, tau])
      (Store.inBlock tau.1 tau.2 1)
      (fun μ' => μ'.pos = μ.pos ∧ ∃ t : ℝ, μ'.store.get tau.1 tau.2 = some t ∧
        0.9 * (⨅ i, ‖s - d i‖) ≤ t ∧ t ≤ 1.1 * (⨅ i, ‖s - d i‖)) μ := by
  have hu0 : 0 ≤ u := by simpa using (abs_nonneg _).trans (hM.lit 1)
  have hsd : ∀ i, s ≠ d i := fun i h => by
    have := hdist i; rw [h, sub_self, norm_zero] at this; linarith
  have hm0 : 0 < m := hmq ▸ by positivity
  have hκ1 : 1 ≤ κ := (one_le_pseudoConditionNumber hV.ne_zero).trans hκ
  have hp1 : p ≤ 1 := (hw 0).trans ((Finset.single_le_sum (fun j _ => lastRowWeights_nonneg V j)
    (Finset.mem_univ 0)).trans_eq (sum_lastRowWeights hV))
  have hT := comptauHalf_isHalfTau (shifts := List.replicate (2 * m) s) hS hM hCmp hH hH0 hV
    hHV hκ hC hη₁ (fun z hz => (List.eq_of_mem_replicate hz) ▸ hs)
    (fun z hz => (List.eq_of_mem_replicate hz) ▸ hdist) hnu
    (by rwa [List.length_replicate, Nat.mul_div_cancel_left _ two_pos])
    (by rwa [List.length_replicate, Nat.mul_div_cancel_left _ two_pos])
  refine (distSpec_writes_word hS hm0 hT hl hHs hsp htau hth hts).mono le_rfl ?_
  rintro μ' - ⟨hp', t, ht, hb⟩
  refine ⟨hp', _, ht, ?_⟩
  set R := ‖WithLp.toLp 2 (((s • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) - H)⁻¹ ^ m)
    (Fin.last n))‖ with hR
  obtain ⟨i₀, hi₀⟩ := exists_eq_ciInf_of_finite (f := fun i => ‖s - d i‖)
  have hD : 0 < ⨅ i, ‖s - d i‖ := by rw [← hi₀]; exact norm_pos_iff.mpr (sub_ne_zero.mpr (hsd i₀))
  have hκV := (pseudoConditionNumber_nonneg V).trans hκ
  have hb₁ := sqrt_lastRowWeights_mul_le_norm_lastRow_inv_pow (m := m) hV hHV hsd i₀
  rw [← hR, hi₀] at hb₁
  have hsw : √p ≤ √(lastRowWeights V i₀) := Real.sqrt_le_sqrt (hw i₀)
  have hDm : 0 < (⨅ i, ‖s - d i‖) ^ m := pow_pos hD m
  have hRpos : 0 < R := by
    by_contra h
    have hR0 : R = 0 := le_antisymm (not_lt.mp h) (norm_nonneg _)
    rw [hR0, mul_zero] at hb₁
    have : 0 < √(lastRowWeights V i₀) * (⨅ i, ‖s - d i‖)⁻¹ ^ m :=
      mul_pos ((Real.sqrt_pos.mpr hp).trans_le hsw) (by positivity)
    linarith
  have ha := norm_lastRow_inv_pow_le (m := m) hV hHV hsd
  rw [← hR] at ha
  refine distSpec_root_bounds hκ1 hp hp1 hm0 hm hD (inv_nonneg.mpr hRpos.le) ?_ ?_
    (abs_distSpecWord_sub_le hM hu0 (by subst hmq; exact_mod_cast hum) (Real.rpow_nonneg
      (inv_nonneg.mpr hRpos.le) _) (by rwa [← hmq, Real.rpow_inv_natCast_pow
        (inv_nonneg.mpr hRpos.le) hm0.ne']))
  · -- `R ≤ κ D⁻ᵐ`
    rw [← div_eq_mul_inv, le_div_iff₀ hRpos]
    calc (⨅ i, ‖s - d i‖) ^ m * R ≤ (⨅ i, ‖s - d i‖) ^ m * (κ * (⨅ i, ‖s - d i‖)⁻¹ ^ m) := by
          gcongr; exact ha.trans (by gcongr)
      _ = κ := by rw [inv_pow]; field_simp
  · -- `√p D⁻ᵐ ≤ κ R`
    rw [← div_eq_mul_inv, div_le_iff₀ hRpos]
    have h1 : √p * (⨅ i, ‖s - d i‖)⁻¹ ^ m ≤ κ * R :=
      ((mul_le_mul_of_nonneg_right hsw (by positivity)).trans hb₁).trans
        (mul_le_mul_of_nonneg_right hκ (norm_nonneg _))
    rw [inv_pow] at h1
    calc √p = √p * ((⨅ i, ‖s - d i‖) ^ m)⁻¹ * (⨅ i, ‖s - d i‖) ^ m := by field_simp
      _ ≤ κ * R * (⨅ i, ‖s - d i‖) ^ m := by gcongr
      _ = κ * (⨅ i, ‖s - d i‖) ^ m * R := by ring

/-- `DistSpec` terminates on every tape: on a scalar machine with exact comparisons and the
literal $0$ exact, from any matrix of order $n + 1$ at `h`, any shift pair and room for the word
`tau`, for every degree $m$ (zero included) and $q$,
`NLAlib.SmallEig.distSpec` writes only that word, keeps the tape position and stores a word
there. -/
theorem distSpec_terminates {M : Machine ℝ} {I : Interp O Q ℝ} (hS : IsScalar M I)
    (hzero : M.lit 0 = 0) (hCmp : IsCmp id I) {n m q : ℕ}
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {s : ℂ}
    {τ : Tape ℝ} {μ : Mem ℝ} {h sp tau : ℕ × ℕ} (hl : μ.Live [h, sp, tau])
    (hHs : HoldsMatrix h H μ.store) (hsp : μ.store.readBlock sp.1 sp.2 2 = some [s.re, s.im])
    (htau : tau.2 < μ.store.len tau.1) :
    Writes .total I τ (distSpec (O := O) (Q := Q)).body (Env.frame [n + 1, m, q] [h, sp, tau])
      (Store.inBlock tau.1 tau.2 1)
      (fun μ' => μ'.pos = μ.pos ∧ ∃ t : ℝ, μ'.store.get tau.1 tau.2 = some t) μ := by
  unfold distSpec
  refine (comptauHalf_terminates (h := 1) (e := m) hS hzero hCmp hl hHs
    (by simpa using hsp) htau).frame_seq_le rfl rfl hl le_rfl ?_
  rintro μ₁ - ⟨hp₁, t, ht⟩
  refine ((squareRoots_writes_word (τ := τ) (k := q) hS ht).in_frame rfl rfl
    (by simpa [Mem.Live] using Store.lt_length_of_get ht)).mono le_rfl ?_
  rintro μ₂ - ⟨hp₂, hR₂⟩
  exact ⟨hp₂.trans hp₁, _, hR₂⟩

end Theorems

end NLAlib.SmallEig
