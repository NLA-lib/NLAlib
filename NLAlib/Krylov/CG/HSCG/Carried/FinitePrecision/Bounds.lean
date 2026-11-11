/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.CG.HSCG.Carried.Rounded
public import NLAlib.ForMathlib.Analysis.InnerProductSpace.PiL2

/-!
# Normwise consequences of the rounded CG operation contracts

The componentwise BLAS contracts imply the Euclidean local-error model used by the existing
finite-precision CG mathematics. These bridges include zero vectors and zero scalar targets;
no division by a target is assumed in their statements.

## Main results

* `NLAlib.Krylov.CG.HSCG.Carried.Rounded.norm_update_le` converts vector envelopes.
* `NLAlib.Krylov.CG.HSCG.Carried.Rounded.exists_relative_error` extracts scalar defects.
* `NLAlib.Krylov.CG.HSCG.Carried.Rounded.sum_abs_mul_le` bounds dot-product envelopes.
-/

@[expose] public section

namespace NLAlib.Krylov.CG.HSCG.Carried.Rounded

open Ops
open scoped Matrix

variable {ι : Type*} [Fintype ι]

/-- The absolute-product envelope of a dot product is bounded by the two Euclidean norms.
This is Cauchy–Schwarz applied to coordinatewise absolute values. [Higham2002, §3.1]. -/
theorem sum_abs_mul_le (x y : ι → ℝ) :
    ∑ i, |x i * y i| ≤ ‖WithLp.toLp 2 x‖ * ‖WithLp.toLp 2 y‖ := by
  calc
    _ ≤ |(fun i => |x i|) ⬝ᵥ (fun i => |y i|)| := by
      simpa only [dotProduct, abs_mul] using le_abs_self (∑ i, |x i| * |y i|)
    _ ≤ _ := by
      simpa [EuclideanSpace.norm_eq] using
        EuclideanSpace.abs_dotProduct_le_norm (fun i => |x i|) (fun i => |y i|)

/-- A componentwise axpy envelope implies its Euclidean forward-error bound, including zero
coefficients and empty vectors. [Higham2002, §2.2]. -/
theorem norm_update_le {e a : ℝ} (he : 0 ≤ e) {x y z : ι → ℝ}
    (h : ∀ i, |z i - (y i + a * x i)| ≤ e * (|y i| + |a * x i|)) :
    ‖WithLp.toLp 2 (z - (y + a • x))‖ ≤
      e * (‖WithLp.toLp 2 y‖ + |a| * ‖WithLp.toLp 2 x‖) := by
  have hnorm := EuclideanSpace.norm_toLp_le_norm_toLp
    (x := z - (y + a • x))
    (y := e • ((fun i => |y i|) + |a| • (fun i => |x i|))) fun i => by
      change |z i - (y i + a * x i)| ≤ |e * (|y i| + |a| * |x i|)|
      rw [abs_mul, abs_of_nonneg he,
        abs_of_nonneg (show 0 ≤ |y i| + |a| * |x i| by positivity)]
      simpa only [abs_mul] using h i
  refine hnorm.trans ?_
  rw [WithLp.toLp_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg he,
    WithLp.toLp_add, WithLp.toLp_smul]
  refine (mul_le_mul_of_nonneg_left (norm_add_le _ _) he).trans_eq ?_
  rw [norm_smul, Real.norm_eq_abs, abs_abs]
  congr 2 <;> simp [EuclideanSpace.norm_eq]

/-- A forward relative-error inequality yields a multiplicative defect even when its exact
target is zero. [Higham2002, (2.4)]. -/
theorem exists_relative_error {e v t : ℝ} (he : 0 ≤ e) (h : |v - t| ≤ e * |t|) :
    ∃ d : ℝ, |d| ≤ e ∧ v = t * (1 + d) := by
  by_cases ht : t = 0
  · have hv : v = 0 := abs_eq_zero.mp (le_antisymm
      (by simpa only [ht, sub_zero, abs_zero, mul_zero] using h) (abs_nonneg _))
    exact ⟨0, by simpa using he, by simp [ht, hv]⟩
  · refine ⟨(v - t) / t, ?_, ?_⟩
    · rw [abs_div]
      exact (div_le_iff₀ (abs_pos.mpr ht)).mpr h
    · field_simp
      ring

/-- A self-dot envelope is a relative squared-norm error, including an exactly zero vector.
[Higham2002, (3.5)]. -/
theorem self_dot_relative {e v : ℝ} (he : 0 ≤ e) (x : ι → ℝ)
    (h : |v - x ⬝ᵥ x| ≤ e * ∑ i, |x i * x i|) :
    ∃ d : ℝ, |d| ≤ e ∧ v = ‖WithLp.toLp 2 x‖ ^ 2 * (1 + d) := by
  apply exists_relative_error he
  rw [EuclideanSpace.norm_toLp_sq_eq_dotProduct_self]
  have hs : ∑ i, |x i * x i| = x ⬝ᵥ x := by
    unfold dotProduct
    exact Finset.sum_congr rfl fun i _ => abs_of_nonneg (mul_self_nonneg _)
  rw [abs_of_nonneg (show 0 ≤ x ⬝ᵥ x from
    Finset.sum_nonneg fun i _ => mul_self_nonneg _)]
  rwa [hs] at h

/-- Every local standard CG recurrence supplies the existing run theory's normwise scalar
and vector defects at a common error bound. The matvec defect is zero. [Higham2002, §3.1]. -/
theorem RoundBounds.exists_run_errors {n : ℕ} {u ed ea e : ℝ}
    {A : Matrix (Fin n) (Fin n) ℝ} {s s' : CGState ℝ (Fin n)} {rho rho' : ℝ}
    (h : RoundBounds u ed ea A s s' rho rho') (hu : 0 ≤ u) (hd : 0 ≤ ed) (ha : 0 ≤ ea)
    (hue : u ≤ e) (hde : ed ≤ e) (hae : ea ≤ e) :
    ∃ curv alpha beta theta eg eb : ℝ,
      0 < rho ∧ 0 < curv ∧
      rho' = ‖WithLp.toLp 2 s'.r‖ ^ 2 * (1 + theta) ∧ |theta| ≤ e ∧
      |s.p ⬝ᵥ (A *ᵥ s.p) - curv| ≤
        e * ‖WithLp.toLp 2 s.p‖ * ‖WithLp.toLp 2 (A *ᵥ s.p)‖ ∧
      alpha = rho / curv * (1 + eg) ∧ |eg| ≤ e ∧
      beta = rho' / rho * (1 + eb) ∧ |eb| ≤ e ∧
      ‖WithLp.toLp 2 (s.x + alpha • s.p - s'.x)‖ ≤
        e * (‖WithLp.toLp 2 s.x‖ + |alpha| * ‖WithLp.toLp 2 s.p‖) ∧
      ‖WithLp.toLp 2 (s.r - alpha • (A *ᵥ s.p) - s'.r)‖ ≤
        e * (‖WithLp.toLp 2 s.r‖ + |alpha| * ‖WithLp.toLp 2 (A *ᵥ s.p)‖) ∧
      ‖WithLp.toLp 2 (s'.r + beta • s.p - s'.p)‖ ≤
        e * (‖WithLp.toLp 2 s'.r‖ + |beta| * ‖WithLp.toLp 2 s.p‖) := by
  obtain ⟨curv, alpha, beta, hrho, hcurv, hc, halpha, hx, hr, hrho', hbeta, hp⟩ := h
  obtain ⟨theta, htheta, hetheta⟩ := self_dot_relative hd s'.r hrho'
  obtain ⟨eg, heg, healpha⟩ := exists_relative_error hu halpha
  obtain ⟨eb, heb, hebeta⟩ := exists_relative_error hu hbeta
  have hvec {a : ℝ} {x y z : Fin n → ℝ}
      (hh : ∀ i, |z i - (y i + a * x i)| ≤ ea * (|y i| + |a * x i|)) :
      ‖WithLp.toLp 2 (y + a • x - z)‖ ≤
        e * (‖WithLp.toLp 2 y‖ + |a| * ‖WithLp.toLp 2 x‖) := by
    rw [← neg_sub z, WithLp.toLp_neg, norm_neg]
    exact (norm_update_le ha hh).trans (mul_le_mul_of_nonneg_right hae (by positivity))
  refine ⟨curv, alpha, beta, theta, eg, eb, hrho, hcurv, hetheta, htheta.trans hde,
    ?_, healpha, heg.trans hue, hebeta, heb.trans hue, hvec hx, ?_, hvec hp⟩
  · have hnorm := sum_abs_mul_le s.p (A *ᵥ s.p)
    calc
      _ ≤ ed * ∑ i, |s.p i * (A *ᵥ s.p) i| := by simpa only [abs_sub_comm] using hc
      _ ≤ ed * (‖WithLp.toLp 2 s.p‖ * ‖WithLp.toLp 2 (A *ᵥ s.p)‖) :=
        mul_le_mul_of_nonneg_left hnorm hd
      _ ≤ e * (‖WithLp.toLp 2 s.p‖ * ‖WithLp.toLp 2 (A *ᵥ s.p)‖) :=
        mul_le_mul_of_nonneg_right hde (by positivity)
      _ = _ := (mul_assoc ..).symm
  · have hh := hvec (a := -alpha) (x := A *ᵥ s.p) (y := s.r) (z := s'.r)
      (by simpa only [neg_mul, ← sub_eq_add_neg, abs_neg] using hr)
    simpa only [sub_eq_add_neg, neg_smul, abs_neg] using hh

end NLAlib.Krylov.CG.HSCG.Carried.Rounded
