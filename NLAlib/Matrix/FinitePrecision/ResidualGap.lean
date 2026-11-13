/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Basic.QuadForm
public import NLAlib.Matrix.Norms.Spectral

/-!
# Residual gaps and physical quadratic errors from update defects

An inexact matrix-vector product and two inexact vector updates determine the residual
gap directly. The matrix may be rectangular, and coefficients may have either sign or
be zero. These identities do not use a relative arithmetic model or divide by a computed
coefficient. Absolute rounding errors can therefore be retained in the local defects.

The quadratic perturbation bound acts directly on the physical iterate error. It requires
neither a residual-to-error conversion nor positive definiteness.

## Main results

* `NLAlib.sub_mulVec_sub_succ`: exact one-step residual-gap identity.
* `NLAlib.norm_sub_mulVec_sub_succ_le`: one-step norm bound.
* `NLAlib.norm_sub_mulVec_sub_le_norm_add_sum`: accumulated gap, including its initial value.
* `NLAlib.norm_quadForm_add_sub_le`: direct physical quadratic perturbation bound.
-/

@[expose] public section

namespace NLAlib

open scoped Matrix

variable {𝕜 : Type*} [RCLike 𝕜] {m n : Type*} [Fintype m] [Fintype n]

omit [Fintype m] in
/-- If a matvec and the iterate/residual updates have defects respectively
$\mathbf{e}^s$, $\mathbf{e}^x$ and $\mathbf{e}^r$, their residual gap changes by
$\alpha\mathbf{e}^s-\mathbf{A}\mathbf{e}^x-\mathbf{e}^r$. The coefficient may be zero. -/
theorem sub_mulVec_sub_succ (A : Matrix m n 𝕜) (b : m → 𝕜)
    (x p ex : ℕ → n → 𝕜) (r s es er : ℕ → m → 𝕜) (α : ℕ → 𝕜) (j : ℕ)
    (hs : s j = A *ᵥ p j + es j)
    (hx : x (j + 1) = x j + α j • p j + ex j)
    (hr : r (j + 1) = r j - α j • s j + er j) :
    b - A *ᵥ x (j + 1) - r (j + 1) =
      (b - A *ᵥ x j - r j) + α j • es j - A *ᵥ ex j - er j := by
  rw [hx, hr, hs]
  simp only [Matrix.mulVec_add, Matrix.mulVec_smul, smul_add]
  abel

/-- A single residual-gap increment is bounded by the matvec, iterate and residual
defects. The rectangular matrix and arbitrary scalar coefficient need no sign assumptions. -/
theorem norm_sub_mulVec_sub_succ_le (A : Matrix m n 𝕜) (b : m → 𝕜)
    (x p ex : ℕ → n → 𝕜) (r s es er : ℕ → m → 𝕜) (α : ℕ → 𝕜) (j : ℕ)
    (hs : s j = A *ᵥ p j + es j)
    (hx : x (j + 1) = x j + α j • p j + ex j)
    (hr : r (j + 1) = r j - α j • s j + er j) :
    ‖WithLp.toLp 2 (b - A *ᵥ x (j + 1) - r (j + 1))‖ ≤
      ‖WithLp.toLp 2 (b - A *ᵥ x j - r j)‖ +
        ‖α j‖ * ‖WithLp.toLp 2 (es j)‖ +
        specNorm A * ‖WithLp.toLp 2 (ex j)‖ + ‖WithLp.toLp 2 (er j)‖ := by
  rw [sub_mulVec_sub_succ A b x p ex r s es er α j hs hx hr]
  simp only [WithLp.toLp_sub, WithLp.toLp_add, WithLp.toLp_smul]
  have h₁ := norm_sub_le
    (WithLp.toLp 2 (b - A *ᵥ x j - r j) + α j • WithLp.toLp 2 (es j) -
      WithLp.toLp 2 (A *ᵥ ex j)) (WithLp.toLp 2 (er j))
  have h₂ := norm_sub_le
    (WithLp.toLp 2 (b - A *ᵥ x j - r j) + α j • WithLp.toLp 2 (es j))
    (WithLp.toLp 2 (A *ᵥ ex j))
  have h₃ := norm_add_le (WithLp.toLp 2 (b - A *ᵥ x j - r j))
    (α j • WithLp.toLp 2 (es j))
  rw [norm_smul] at h₃
  simp only [WithLp.toLp_sub] at h₁ h₂ h₃
  have h₄ := norm_toLp_mulVec_le A (ex j)
  linarith

/-- Over any finite prefix satisfying the three defect update equations, the residual
gap is bounded by its initial norm plus the sum of the local defect bounds. No assumption
is imposed on the initial gap, coefficient signs, or positivity of a cached scalar. -/
theorem norm_sub_mulVec_sub_le_norm_add_sum (A : Matrix m n 𝕜) (b : m → 𝕜)
    (x p ex : ℕ → n → 𝕜) (r s es er : ℕ → m → 𝕜) (α : ℕ → 𝕜) (k : ℕ)
    (hs : ∀ j < k, s j = A *ᵥ p j + es j)
    (hx : ∀ j < k, x (j + 1) = x j + α j • p j + ex j)
    (hr : ∀ j < k, r (j + 1) = r j - α j • s j + er j) :
    ‖WithLp.toLp 2 (b - A *ᵥ x k - r k)‖ ≤
      ‖WithLp.toLp 2 (b - A *ᵥ x 0 - r 0)‖ +
        ∑ j ∈ Finset.range k, (‖α j‖ * ‖WithLp.toLp 2 (es j)‖ +
          specNorm A * ‖WithLp.toLp 2 (ex j)‖ + ‖WithLp.toLp 2 (er j)‖) := by
  suffices h : ∀ l ≤ k, ‖WithLp.toLp 2 (b - A *ᵥ x l - r l)‖ ≤
      ‖WithLp.toLp 2 (b - A *ᵥ x 0 - r 0)‖ +
        ∑ j ∈ Finset.range l, (‖α j‖ * ‖WithLp.toLp 2 (es j)‖ +
          specNorm A * ‖WithLp.toLp 2 (ex j)‖ + ‖WithLp.toLp 2 (er j)‖) from h k le_rfl
  intro l hl
  induction l with
  | zero => simp only [Finset.sum_range_zero, add_zero, le_refl]
  | succ l ih =>
    rw [Finset.sum_range_succ]
    have hlt : l < k := by omega
    have hstep := norm_sub_mulVec_sub_succ_le A b x p ex r s es er α l
      (hs l hlt) (hx l hlt) (hr l hlt)
    linarith [ih (by omega)]

/-- Perturbing a physical error vector by $\mathbf{d}$ changes its quadratic form by at
most $\|\mathbf{A}\|_2(2\|\mathbf{e}\|\|\mathbf{d}\|+\|\mathbf{d}\|^2)$.
This direct bound holds for real or complex matrices without symmetry or positivity.
In an iterate update the perturbation can be the negative update defect itself. -/
theorem norm_quadForm_add_sub_le (A : Matrix n n 𝕜) (e d : n → 𝕜) :
    ‖quadForm A (e + d) - quadForm A e‖ ≤
      specNorm A * (2 * ‖WithLp.toLp 2 e‖ * ‖WithLp.toLp 2 d‖ +
        ‖WithLp.toLp 2 d‖ ^ 2) := by
  have hid : quadForm A (e + d) - quadForm A e =
      star e ⬝ᵥ (A *ᵥ d) + star d ⬝ᵥ (A *ᵥ e) + quadForm A d := by
    rw [quadForm_add_right]
    ring
  rw [hid]
  have h₁ := norm_add_le (star e ⬝ᵥ (A *ᵥ d) + star d ⬝ᵥ (A *ᵥ e)) (quadForm A d)
  have h₂ := norm_add_le (star e ⬝ᵥ (A *ᵥ d)) (star d ⬝ᵥ (A *ᵥ e))
  have h₃ := norm_star_dotProduct_mulVec_le A e d
  have h₄ := norm_star_dotProduct_mulVec_le A d e
  have h₅ := norm_star_dotProduct_mulVec_le A d d
  change ‖quadForm A d‖ ≤ _ at h₅
  nlinarith

end NLAlib
