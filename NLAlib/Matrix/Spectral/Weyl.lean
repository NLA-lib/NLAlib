/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.ForMathlib.LinearAlgebra.Matrix.Rank
public import NLAlib.Matrix.Spectral.CourantFischer

/-!
# Weyl's inequalities and eigenvalue perturbation

Eigenvalues of Hermitian matrices are monotone in the Loewner order, subadditive in Weyl's sense,
`1`-Lipschitz in the spectral norm, and move by at most `r` positions under a perturbation of
rank `r`.

`NLAlib.eigengap A k` is the gap `eigenvalue A (k - 1) - eigenvalue A k` separating the `k`
largest eigenvalues from the rest; it is the quantity perturbation bounds for eigenspaces divide
by.

## Main definitions

* `NLAlib.eigengap`: the gap below the `k` largest eigenvalues.

## Main results

* `NLAlib.eigenvalue_le_eigenvalue_of_le`: monotonicity in the Loewner order.
* `NLAlib.eigenvalue_add_le`, `NLAlib.le_eigenvalue_add`: Weyl's inequalities.
* `NLAlib.abs_eigenvalue_sub_le`: eigenvalues are `1`-Lipschitz in the spectral norm.
* `NLAlib.eigenvalue_add_le_of_rank_le`, `NLAlib.eigenvalue_le_eigenvalue_add_of_rank_le`:
  interlacing under a low-rank perturbation.
* `NLAlib.abs_eigengap_sub_le`: stability of the gap.
-/

@[expose] public section

open scoped Matrix ComplexOrder MatrixOrder

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n]

/-! ### Perturbations restricted to their kernel -/

/-- The quadratic form of `A + B` agrees with that of `A` on the kernel of `B`. -/
private theorem quadForm_add_of_mem_ker (A : Matrix n n 𝕜) {B : Matrix n n 𝕜} {x : n → 𝕜}
    (hx : x ∈ LinearMap.ker B.mulVecLin) : quadForm (A + B) x = quadForm A x := by
  rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hx
  rw [quadForm_add_left, quadForm_def B, hx, dotProduct_zero, add_zero]

/-! ### Monotonicity -/

/-- **Monotonicity of eigenvalues.** If `A ≤ B` in the Loewner order and `A` is Hermitian (then
so is `B`), every eigenvalue of `A` is at most the corresponding eigenvalue of `B`.
[HornJohnson2013, Corollary 4.3.12].
Port of `Matrix.IsHermitian.eigenvalues₀_le_eigenvalues₀_of_le`.
Result: eigenvalue-monotonicity -/
theorem eigenvalue_le_eigenvalue_of_le {A B : Matrix n n 𝕜} (h : A ≤ B) (hA : A.IsHermitian)
    (k : ℕ) : eigenvalue A k ≤ eigenvalue B k := by
  rcases le_or_gt (Fintype.card n) k with hk | hk
  · rw [eigenvalue_of_card_le A hk, eigenvalue_of_card_le B hk]
  · have hB : B.IsHermitian := by
      have h' := hA.add (Matrix.le_iff.mp h).isHermitian
      rwa [add_sub_cancel] at h'
    obtain ⟨S, hS, hAS⟩ := hA.exists_submodule_eigenvalue_mul_le hk
    exact hB.le_eigenvalue_of_forall_mem S hS.ge fun x hx =>
      (hAS x hx).trans (re_quadForm_le_re_quadForm_of_le h x)

/-- Adding a positive semidefinite matrix does not decrease any eigenvalue. -/
theorem eigenvalue_le_eigenvalue_add_of_posSemidef {A B : Matrix n n 𝕜} (hA : A.IsHermitian)
    (hB : B.PosSemidef) (k : ℕ) : eigenvalue A k ≤ eigenvalue (A + B) k := by
  refine eigenvalue_le_eigenvalue_of_le (Matrix.le_iff.mpr ?_) hA k
  rwa [add_sub_cancel_left]

/-! ### Weyl's inequalities -/

/-- **Weyl's inequality.** For Hermitian `A`, `B` and `i + j` a valid index,
`λ_{i+j}(A + B) ≤ λ_i(A) + λ_j(B)`, eigenvalues non-increasing and indexed from `0`.
[HornJohnson2013, Theorem 4.3.1]; stated there over `ℂ` with eigenvalues in increasing order.
Port of `Matrix.IsHermitian.eigenvalues₀_add_le`.
Result: weyl-inequality -/
theorem eigenvalue_add_le {A B : Matrix n n 𝕜} (hA : A.IsHermitian) (hB : B.IsHermitian)
    {i j : ℕ} (hij : i + j < Fintype.card n) :
    eigenvalue (A + B) (i + j) ≤ eigenvalue A i + eigenvalue B j := by
  obtain ⟨W₁, h₁, hA₁⟩ := hA.exists_submodule_le_eigenvalue_mul (k := i) (by omega)
  obtain ⟨W₂, h₂, hB₂⟩ := hB.exists_submodule_le_eigenvalue_mul (k := j) (by omega)
  refine (hA.add hB).eigenvalue_le_of_forall_mem hij (W₁ ⊓ W₂) ?_ fun x hx => ?_
  · have h := Submodule.finrank_add_finrank_le_card_add_finrank_inf W₁ W₂
    omega
  · rw [quadForm_add_left, map_add, add_mul]
    exact add_le_add (hA₁ x hx.1) (hB₂ x hx.2)

/-- **Weyl's inequality, lower form.** For Hermitian `A`, `B` and valid indices with
`i + j + 1 = k + Fintype.card n`, `λ_i(A) + λ_j(B) ≤ λ_k(A + B)`.
[HornJohnson2013, Theorem 4.3.1].
Result: weyl-inequality -/
theorem le_eigenvalue_add {A B : Matrix n n 𝕜} (hA : A.IsHermitian) (hB : B.IsHermitian)
    {i j k : ℕ} (hi : i < Fintype.card n) (hj : j < Fintype.card n)
    (h : i + j + 1 = k + Fintype.card n) :
    eigenvalue A i + eigenvalue B j ≤ eigenvalue (A + B) k := by
  obtain ⟨S₁, h₁, hA₁⟩ := hA.exists_submodule_eigenvalue_mul_le hi
  obtain ⟨S₂, h₂, hB₂⟩ := hB.exists_submodule_eigenvalue_mul_le hj
  refine (hA.add hB).le_eigenvalue_of_forall_mem (S₁ ⊓ S₂) ?_ fun x hx => ?_
  · have h' := Submodule.finrank_add_finrank_le_card_add_finrank_inf S₁ S₂
    omega
  · rw [quadForm_add_left, map_add, add_mul]
    exact add_le_add (hA₁ x hx.1) (hB₂ x hx.2)

/-- Weyl's inequality with the largest eigenvalue of the perturbation:
`λ_k(A + B) ≤ λ_k(A) + λ_0(B)`. -/
theorem eigenvalue_add_le_add_eigenvalue_zero {A B : Matrix n n 𝕜} (hA : A.IsHermitian)
    (hB : B.IsHermitian) {k : ℕ} (hk : k < Fintype.card n) :
    eigenvalue (A + B) k ≤ eigenvalue A k + eigenvalue B 0 := by
  exact eigenvalue_add_le hA hB (i := k) (j := 0) hk

/-- Weyl's inequality with the smallest eigenvalue of the perturbation:
`λ_k(A) + λ_min(B) ≤ λ_k(A + B)`. -/
theorem eigenvalue_add_eigenvalue_last_le {A B : Matrix n n 𝕜} (hA : A.IsHermitian)
    (hB : B.IsHermitian) {k l : ℕ} (hk : k < Fintype.card n) (hl : l + 1 = Fintype.card n) :
    eigenvalue A k + eigenvalue B l ≤ eigenvalue (A + B) k := by
  exact le_eigenvalue_add hA hB hk (by omega) (by omega)

/-- One side of the Lipschitz bound, at a valid index. -/
private theorem eigenvalue_sub_le_specNorm_sub {A B : Matrix n n 𝕜} (hA : A.IsHermitian)
    (hB : B.IsHermitian) {k : ℕ} (hk : k < Fintype.card n) :
    eigenvalue A k - eigenvalue B k ≤ specNorm (A - B) := by
  have h := eigenvalue_add_le_add_eigenvalue_zero hB (hA.sub hB) hk
  rw [add_sub_cancel] at h
  have h' := (abs_le.mp ((hA.sub hB).abs_eigenvalue_le_specNorm 0)).2
  linarith

/-- **Eigenvalues are `1`-Lipschitz in the spectral norm.** For Hermitian `A`, `B` and every
`k`, `|λ_k(A) - λ_k(B)| ≤ ‖A - B‖₂`.
[HornJohnson2013, Corollary 4.3.15].
Result: weyl-perturbation -/
theorem abs_eigenvalue_sub_le {A B : Matrix n n 𝕜} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (k : ℕ) : |eigenvalue A k - eigenvalue B k| ≤ specNorm (A - B) := by
  rcases le_or_gt (Fintype.card n) k with hk | hk
  · rw [eigenvalue_of_card_le A hk, eigenvalue_of_card_le B hk, sub_self, abs_zero]
    exact specNorm_nonneg _
  · rw [abs_sub_le_iff]
    refine ⟨eigenvalue_sub_le_specNorm_sub hA hB hk, ?_⟩
    rw [specNorm_sub_comm]
    exact eigenvalue_sub_le_specNorm_sub hB hA hk

/-! ### Low-rank perturbations -/

/-- **Interlacing under a low-rank perturbation, upper.** If `B` has rank at most `r` then
`λ_{k+r}(A + B) ≤ λ_k(A)`.
[HornJohnson2013, Corollary 4.3.5].
Port of `NLAlib.eigenvalues₀_add_le_of_rank_le`, there over `ℝ`.
Result: low-rank-interlacing -/
theorem eigenvalue_add_le_of_rank_le {A B : Matrix n n 𝕜} (hA : A.IsHermitian)
    (hB : B.IsHermitian) {r : ℕ} (hr : B.rank ≤ r) {k : ℕ} (hk : k + r < Fintype.card n) :
    eigenvalue (A + B) (k + r) ≤ eigenvalue A k := by
  obtain ⟨W, hW, hAW⟩ := hA.exists_submodule_le_eigenvalue_mul (k := k) (by omega)
  refine (hA.add hB).eigenvalue_le_of_forall_mem hk (W ⊓ LinearMap.ker B.mulVecLin) ?_
    fun x hx => ?_
  · have h₁ := Submodule.finrank_add_finrank_le_card_add_finrank_inf W (LinearMap.ker B.mulVecLin)
    have h₂ := Matrix.finrank_ker_mulVecLin_add_rank B
    omega
  · rw [quadForm_add_of_mem_ker A hx.2]
    exact hAW x hx.1

/-- **Interlacing under a low-rank perturbation, lower.** If `B` has rank at most `r` then
`λ_{k+r}(A) ≤ λ_k(A + B)`.
[HornJohnson2013, Corollary 4.3.5].
Port of `NLAlib.eigenvalues₀_le_add_of_rank_le`, there over `ℝ`.
Result: low-rank-interlacing -/
theorem eigenvalue_le_eigenvalue_add_of_rank_le {A B : Matrix n n 𝕜} (hA : A.IsHermitian)
    (hB : B.IsHermitian) {r : ℕ} (hr : B.rank ≤ r) {k : ℕ} (hk : k + r < Fintype.card n) :
    eigenvalue A (k + r) ≤ eigenvalue (A + B) k := by
  obtain ⟨W, hW, hW'⟩ := (hA.add hB).exists_submodule_le_eigenvalue_mul (k := k) (by omega)
  refine hA.eigenvalue_le_of_forall_mem hk (W ⊓ LinearMap.ker B.mulVecLin) ?_ fun x hx => ?_
  · have h₁ := Submodule.finrank_add_finrank_le_card_add_finrank_inf W (LinearMap.ker B.mulVecLin)
    have h₂ := Matrix.finrank_ker_mulVecLin_add_rank B
    omega
  · rw [← quadForm_add_of_mem_ker A hx.2]
    exact hW' x hx.1

/-- **Rank-one update, upper.** Adding `z zᴴ` moves each eigenvalue up by at most one position:
`λ_{k+1}(A + z zᴴ) ≤ λ_k(A)`. [HornJohnson2013, Corollary 4.3.9].
Port of `NLAlib.eigenvalues₀_rank_one_add_interlacing`, there over `ℝ` as a conjunction. -/
theorem eigenvalue_add_vecMulVec_star_le {A : Matrix n n 𝕜} (hA : A.IsHermitian) (z : n → 𝕜)
    {k : ℕ} (hk : k + 1 < Fintype.card n) :
    eigenvalue (A + Matrix.vecMulVec z (star z)) (k + 1) ≤ eigenvalue A k := by
  exact eigenvalue_add_le_of_rank_le hA (Matrix.posSemidef_vecMulVec_self_star z).isHermitian
    (Matrix.rank_vecMulVec_le z (star z)) hk

/-- **Rank-one update, lower.** Adding `z zᴴ` does not decrease any eigenvalue.
[HornJohnson2013, Corollary 4.3.9]. -/
theorem eigenvalue_le_eigenvalue_add_vecMulVec_star {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    (z : n → 𝕜) (k : ℕ) :
    eigenvalue A k ≤ eigenvalue (A + Matrix.vecMulVec z (star z)) k := by
  exact eigenvalue_le_eigenvalue_add_of_posSemidef hA (Matrix.posSemidef_vecMulVec_self_star z) k

/-- **Rank-one downdate, upper.** Subtracting `z zᴴ` does not increase any eigenvalue.
[HornJohnson2013, Corollary 4.3.9]. -/
theorem eigenvalue_sub_vecMulVec_star_le {A : Matrix n n 𝕜} (hA : A.IsHermitian) (z : n → 𝕜)
    (k : ℕ) : eigenvalue (A - Matrix.vecMulVec z (star z)) k ≤ eigenvalue A k := by
  have h := eigenvalue_le_eigenvalue_add_vecMulVec_star
    (hA.sub (Matrix.posSemidef_vecMulVec_self_star z).isHermitian) z k
  rwa [sub_add_cancel] at h

/-- **Rank-one downdate, lower.** Subtracting `z zᴴ` moves each eigenvalue down by at most one
position: `λ_{k+1}(A) ≤ λ_k(A - z zᴴ)`. [HornJohnson2013, Corollary 4.3.9]. -/
theorem eigenvalue_le_eigenvalue_sub_vecMulVec_star {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    (z : n → 𝕜) {k : ℕ} (hk : k + 1 < Fintype.card n) :
    eigenvalue A (k + 1) ≤ eigenvalue (A - Matrix.vecMulVec z (star z)) k := by
  have h := eigenvalue_add_vecMulVec_star_le
    (hA.sub (Matrix.posSemidef_vecMulVec_self_star z).isHermitian) z hk
  rwa [sub_add_cancel] at h

/-! ### The eigengap -/

/-- The **eigengap** below the `k` largest eigenvalues: `λ_{k-1}(A) - λ_k(A)` with eigenvalues
indexed from `0`, the gap that separates the leading `k`-dimensional eigenspace from the rest. The
index is the dimension of that eigenspace. With truncated subtraction `eigengap A 0 = 0`, so a
hypothesis `0 < eigengap A k` already excludes `k = 0`. -/
noncomputable def eigengap (A : Matrix n n 𝕜) (k : ℕ) : ℝ :=
  eigenvalue A (k - 1) - eigenvalue A k

/-- The eigengap at dimension zero is zero. -/
@[simp]
theorem eigengap_zero (A : Matrix n n 𝕜) : eigengap A 0 = 0 := by
  rw [eigengap, Nat.zero_sub, sub_self]

/-- The eigengap at dimension `k + 1` is `λ_k - λ_{k+1}`. This is the form to compute with. -/
theorem eigengap_succ (A : Matrix n n 𝕜) (k : ℕ) :
    eigengap A (k + 1) = eigenvalue A k - eigenvalue A (k + 1) := by
  rw [eigengap, Nat.add_sub_cancel]

/-- The eigengap of a Hermitian matrix is nonnegative at a valid index. -/
theorem _root_.Matrix.IsHermitian.eigengap_nonneg {A : Matrix n n 𝕜} (hA : A.IsHermitian) {k : ℕ}
    (hk : k < Fintype.card n) : 0 ≤ eigengap A k := by
  exact sub_nonneg.mpr (hA.eigenvalue_le_eigenvalue (Nat.sub_le k 1) hk)

/-- **Stability of the eigengap.** A Hermitian perturbation changes the gap by at most twice its
spectral norm. -/
theorem abs_eigengap_sub_le {A B : Matrix n n 𝕜} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (k : ℕ) : |eigengap A k - eigengap B k| ≤ 2 * specNorm (A - B) := by
  have h₁ := abs_le.mp (abs_eigenvalue_sub_le hA hB (k - 1))
  have h₂ := abs_le.mp (abs_eigenvalue_sub_le hA hB k)
  rw [eigengap, eigengap, abs_le]
  constructor <;> linarith

end NLAlib
