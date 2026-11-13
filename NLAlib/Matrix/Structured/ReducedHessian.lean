/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Algebra.Exact.Basic
public import Mathlib.Order.Filter.Extr
public import NLAlib.Matrix.Basic.Gram
public import NLAlib.Matrix.Basic.QuadForm
import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-!
# Equality constraints and the reduced Hessian

For constraints with full row rank, a null-space basis reduces a saddle-point linear system
and describes uniqueness of feasible quadratic minimizers. The basis need not be orthonormal.
[BenziGolubLiesen2005, §6].

For a computed null-space basis, use Mathlib’s `LinearMap.exact_iff` with `Z.mulVecLin`
and `B.mulVecLin` to supply the exactness hypothesis from equality of the range and kernel.

## Main results

* `NLAlib.mulVec_fromBlocks_eq_of_mulVec_eq`: reconstruct a primal solution and its multiplier.
* `NLAlib.isUnit_fromBlocks_iff_isUnit_conjTranspose_mul_mul`: the null-space invertibility test.
* `Matrix.IsHermitian.forall_existsUnique_isMinOn_quadraticObjective_iff`: unique minimizers.
-/

@[expose] public section

open Matrix
open scoped Matrix ComplexOrder

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {m n r : Type*} [Fintype m] [Fintype n] [Fintype r]
variable {B : Matrix m n 𝕜} {Z : Matrix n r 𝕜}

private theorem constraint_gram_isUnit [DecidableEq m] (hB : Function.Injective Bᴴ.mulVec) :
    IsUnit (B * Bᴴ) := by
  simpa only [Matrix.conjTranspose_conjTranspose] using isUnit_conjTranspose_mul_self_iff.mpr hB

omit [Fintype m] in
private theorem mul_eq_zero_of_exact (h : Function.Exact Z.mulVec B.mulVec) : B * Z = 0 := by
  apply Matrix.ext_iff_mulVec.mpr
  intro y
  simpa only [Matrix.mulVec_mulVec, Matrix.zero_mulVec] using h.apply_apply_eq_zero y

private theorem adjoint_mulVec_recovery [DecidableEq m] (h : Function.Exact Z.mulVec B.mulVec)
    (hB : Function.Injective Bᴴ.mulVec) {v : n → 𝕜} (hv : Zᴴ *ᵥ v = 0) :
    Bᴴ *ᵥ ((B * Bᴴ)⁻¹ *ᵥ (B *ᵥ v)) = v := by
  let w := v - Bᴴ *ᵥ ((B * Bᴴ)⁻¹ *ᵥ (B *ᵥ v))
  have hw : B *ᵥ w = 0 := by
    dsimp only [w]
    rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp (constraint_gram_isUnit hB)),
      Matrix.one_mulVec, sub_self]
  obtain ⟨y, hy⟩ := (h w).mp hw
  have hZB : Zᴴ * Bᴴ = 0 := by
    rw [← Matrix.conjTranspose_mul, mul_eq_zero_of_exact h, Matrix.conjTranspose_zero]
  have hzw : Zᴴ *ᵥ w = 0 := by
    dsimp only [w]
    rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, hZB, Matrix.zero_mulVec, hv, sub_zero]
  rw [← hy, Matrix.mulVec_mulVec] at hzw
  have hw0 : w = 0 := hy.symm.trans ((Matrix.conjTranspose_mul_self_mulVec_eq_zero Z y).mp hzw)
  exact (sub_eq_zero.mp hw0).symm

private theorem reduced_eq_iff_stationary (H : Matrix n n 𝕜) (f xp : n → 𝕜) (y : r → 𝕜) :
    (Zᴴ * H * Z) *ᵥ y = Zᴴ *ᵥ (f - H *ᵥ xp) ↔ Zᴴ *ᵥ (f - H *ᵥ (xp + Z *ᵥ y)) = 0 := by
  simp only [← Matrix.mulVec_mulVec, Matrix.mulVec_sub, Matrix.mulVec_add]
  constructor <;> intro h <;> linear_combination -h

/-- **Null-space solution of the saddle-point equations.** Let $\mathbf{B}$ have full row rank
and let the columns of $\mathbf{Z}$ span its kernel. Given a feasible point $\mathbf{x}_p$ and
any solution $\mathbf{y}$ of the reduced equation, the primal solution is
$\mathbf{x}=\mathbf{x}_p+\mathbf{Z}\mathbf{y}$. Its multiplier solves the constraint Gram
system with right-hand side $\mathbf{B}(\mathbf{f}-\mathbf{H}\mathbf{x})$.
[BenziGolubLiesen2005, equations (6.1)–(6.2)].
Result: kkt-reduced-hessian -/
theorem mulVec_fromBlocks_eq_of_mulVec_eq [DecidableEq m] (H : Matrix n n 𝕜)
    (h : Function.Exact Z.mulVec B.mulVec) (hB : Function.Injective Bᴴ.mulVec)
    {f xp : n → 𝕜} {g : m → 𝕜} {y : r → 𝕜} (hxp : B *ᵥ xp = g)
    (hy : (Zᴴ * H * Z) *ᵥ y = Zᴴ *ᵥ (f - H *ᵥ xp)) :
    (fromBlocks H Bᴴ B 0) *ᵥ Sum.elim (xp + Z *ᵥ y)
      ((B * Bᴴ)⁻¹ *ᵥ (B *ᵥ (f - H *ᵥ (xp + Z *ᵥ y)))) = Sum.elim f g := by
  rw [fromBlocks_mulVec]
  simp only [Function.comp_def, Sum.elim_inl, Sum.elim_inr, Matrix.zero_mulVec, add_zero]
  have ht := adjoint_mulVec_recovery h hB ((reduced_eq_iff_stationary H f xp y).mp hy)
  congr 1
  · rw [ht, add_sub_cancel]
  · rw [Matrix.mulVec_add, h.apply_apply_eq_zero, add_zero, hxp]

/-- A primal vector in null-space coordinates that satisfies the stationarity equation solves
its compression by the null-space basis. [BenziGolubLiesen2005, equation (6.1)]. -/
theorem conjTranspose_mul_mul_mulVec_eq_of_add_mulVec_eq (H : Matrix n n 𝕜)
    (h : Function.Exact Z.mulVec B.mulVec) {f xp : n → 𝕜} {y : r → 𝕜} {l : m → 𝕜}
    (he : H *ᵥ (xp + Z *ᵥ y) + Bᴴ *ᵥ l = f) :
    (Zᴴ * H * Z) *ᵥ y = Zᴴ *ᵥ (f - H *ᵥ xp) := by
  apply (reduced_eq_iff_stationary H f xp y).mpr
  rw [← he, add_sub_cancel_left, Matrix.mulVec_mulVec, ← Matrix.conjTranspose_mul,
    mul_eq_zero_of_exact h, Matrix.conjTranspose_zero, Matrix.zero_mulVec]

/-- **Invertibility of a saddle-point matrix.** For a full-row-rank $\mathbf{B}$ and any basis
$\mathbf{Z}$ of its kernel, the block matrix with blocks $\mathbf{H}$,
$\mathbf{B}^{\mathsf{H}}$, $\mathbf{B}$ and zero is invertible exactly when the reduced
matrix $\mathbf{Z}^{\mathsf{H}}\mathbf{H}\mathbf{Z}$ is invertible. The ambient block
$\mathbf{H}$ may be singular or indefinite. [BenziGolubLiesen2005, §3.3 and §6].
Result: kkt-reduced-hessian -/
theorem isUnit_fromBlocks_iff_isUnit_conjTranspose_mul_mul [DecidableEq m] [DecidableEq n]
    [DecidableEq r] (H : Matrix n n 𝕜) (h : Function.Exact Z.mulVec B.mulVec)
    (hB : Function.Injective Bᴴ.mulVec) (hZ : Function.Injective Z.mulVec) :
    IsUnit (fromBlocks H Bᴴ B 0) ↔ IsUnit (Zᴴ * H * Z) := by
  rw [← Matrix.mulVec_injective_iff_isUnit, ← Matrix.mulVec_injective_iff_isUnit,
    ← Matrix.coe_mulVecLin, ← Matrix.coe_mulVecLin, ← LinearMap.ker_eq_bot,
    ← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot', LinearMap.ker_eq_bot']
  constructor
  · intro hinj y hy
    change (Zᴴ * H * Z) *ᵥ y = 0 at hy
    have hy' : (Zᴴ * H * Z) *ᵥ y = Zᴴ *ᵥ (0 - H *ᵥ 0) := by
      simpa only [Matrix.mulVec_zero, sub_zero] using hy
    have hs := mulVec_fromBlocks_eq_of_mulVec_eq H h hB (Matrix.mulVec_zero B) hy'
    simp only [zero_add, Sum.elim_zero_zero] at hs
    have hx := congrArg (fun v => v ∘ Sum.inl) (hinj _ hs)
    change Z *ᵥ y = 0 at hx
    exact hZ (hx.trans (Matrix.mulVec_zero Z).symm)
  · intro hinj v hv
    have hv' : (fromBlocks H Bᴴ B 0) *ᵥ v = 0 := hv
    rw [fromBlocks_mulVec] at hv'
    have htop : H *ᵥ (v ∘ Sum.inl) + Bᴴ *ᵥ (v ∘ Sum.inr) = 0 :=
      funext fun i => congrFun hv' (Sum.inl i)
    have hbot : B *ᵥ (v ∘ Sum.inl) = 0 := by
      simpa only [Matrix.zero_mulVec, add_zero] using
        (show B *ᵥ (v ∘ Sum.inl) + (0 : Matrix m m 𝕜) *ᵥ (v ∘ Sum.inr) = 0 from
          funext fun i => congrFun hv' (Sum.inr i))
    obtain ⟨y, hy⟩ := (h _).mp hbot
    have hs := conjTranspose_mul_mul_mulVec_eq_of_add_mulVec_eq H h
      (xp := 0) (y := y) (by simpa only [zero_add, hy] using htop)
    have hy0 := hinj y (by
      change (Zᴴ * H * Z) *ᵥ y = 0
      simpa only [Matrix.mulVec_zero, sub_self] using hs)
    have hx : v ∘ Sum.inl = 0 := by simpa only [hy0, Matrix.mulVec_zero] using hy.symm
    have hl : v ∘ Sum.inr = 0 := hB (by simpa only [hx, Matrix.mulVec_zero, zero_add] using htop)
    ext i
    cases i with
    | inl i => exact congrFun hx i
    | inr i => exact congrFun hl i


/-- A null-space basis with $\operatorname{range}(\mathbf{Z})=\ker(\mathbf{B})$ gives the
invertibility test for the saddle-point matrix and its reduced Hessian.
[BenziGolubLiesen2005, §6]. -/
theorem isUnit_fromBlocks_iff_isUnit_conjTranspose_mul_mul_of_range_eq_ker
    [DecidableEq m] [DecidableEq n] [DecidableEq r] (H : Matrix n n 𝕜)
    (h : LinearMap.range Z.mulVecLin = LinearMap.ker B.mulVecLin)
    (hB : Function.Injective Bᴴ.mulVec) (hZ : Function.Injective Z.mulVec) :
    IsUnit (fromBlocks H Bᴴ B 0) ↔ IsUnit (Zᴴ * H * Z) :=
  isUnit_fromBlocks_iff_isUnit_conjTranspose_mul_mul H
    ((LinearMap.exact_iff (f := Z.mulVecLin) (g := B.mulVecLin)).2 h.symm) hB hZ

/-- The real-valued quadratic objective with Hessian $\mathbf{H}$ and linear coefficient
$\mathbf{f}$, evaluated at $\mathbf{x}$. [BenziGolubLiesen2005, §1]. -/
noncomputable def quadraticObjective (H : Matrix n n 𝕜) (f x : n → 𝕜) : ℝ :=
  (1 / 2 : ℝ) * RCLike.re (quadForm H x) - RCLike.re (star f ⬝ᵥ x)

/-- At a point stationary along the columns of $\mathbf{Z}$, the quadratic objective increases
by half the reduced quadratic form in the displacement coordinates. -/
theorem quadraticObjective_add_mulVec_eq {H : Matrix n n 𝕜} (f x : n → 𝕜) (hH : H.IsHermitian)
    (hstat : Zᴴ *ᵥ (f - H *ᵥ x) = 0) (y : r → 𝕜) :
    quadraticObjective H f (x + Z *ᵥ y) = quadraticObjective H f x +
      (1 / 2 : ℝ) * RCLike.re (quadForm (Zᴴ * H * Z) y) := by
  have hc : star f ⬝ᵥ (Z *ᵥ y) = star x ⬝ᵥ (H *ᵥ (Z *ᵥ y)) := by
    have hh := congrArg (fun v => star v ⬝ᵥ y) hstat
    rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.conjTranspose_conjTranspose] at hh
    simp only [star_sub, sub_dotProduct, star_zero, zero_dotProduct] at hh
    rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, hH.eq] at hh
    exact sub_eq_zero.mp hh
  rw [quadraticObjective, quadraticObjective, hH.re_quadForm_add, dotProduct_add, map_add,
    quadForm_conjTranspose_mul_mul, hc]
  ring

omit [Fintype m] in
/-- **Strict constrained minimality.** Let $\mathbf{H}$ be Hermitian, and let the columns of
$\mathbf{Z}$ span the kernel of $\mathbf{B}$. If the reduced Hessian is positive definite,
then a stationary point has strictly smaller objective than every other point with the same
constraint value. [BenziGolubLiesen2005, §1 and §6].
Result: kkt-reduced-hessian -/
theorem quadraticObjective_lt_of_mulVec_eq_of_ne {H : Matrix n n 𝕜} (f : n → 𝕜)
    (hH : H.IsHermitian) (h : Function.Exact Z.mulVec B.mulVec) (hG : (Zᴴ * H * Z).PosDef)
    {x v : n → 𝕜} (hstat : Zᴴ *ᵥ (f - H *ᵥ x) = 0) (hv : B *ᵥ v = B *ᵥ x) (hne : v ≠ x) :
    quadraticObjective H f x < quadraticObjective H f v := by
  obtain ⟨y, hy⟩ := (h (v - x)).mp (by rw [Matrix.mulVec_sub, hv, sub_self])
  have hy0 : y ≠ 0 := by
    rintro rfl
    exact hne (sub_eq_zero.mp (hy.symm.trans (Matrix.mulVec_zero Z)))
  have he := quadraticObjective_add_mulVec_eq f x hH hstat y
  rw [hy, add_sub_cancel] at he
  rw [he]
  have hp := hG.re_quadForm_pos hy0
  linarith

private theorem existsUnique_feasible_min {H : Matrix n n 𝕜}
    (hH : H.IsHermitian) (h : Function.Exact Z.mulVec B.mulVec) (hB : Function.Injective Bᴴ.mulVec)
    (hG : (Zᴴ * H * Z).PosDef) (f : n → 𝕜) (g : m → 𝕜) :
    ∃! x, B *ᵥ x = g ∧ IsMinOn (quadraticObjective H f) {v | B *ᵥ v = g} x := by
  classical
  let xp := Bᴴ *ᵥ ((B * Bᴴ)⁻¹ *ᵥ g)
  have hxp : B *ᵥ xp = g := by
    dsimp only [xp]
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp (constraint_gram_isUnit hB)),
      Matrix.one_mulVec]
  let y := (Zᴴ * H * Z)⁻¹ *ᵥ (Zᴴ *ᵥ (f - H *ᵥ xp))
  have hy : (Zᴴ * H * Z) *ᵥ y = Zᴴ *ᵥ (f - H *ᵥ xp) := by
    dsimp only [y]
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp
      hG.isUnit), Matrix.one_mulVec]
  let x := xp + Z *ᵥ y
  have hx : B *ᵥ x = g := by
    dsimp only [x]
    rw [Matrix.mulVec_add, h.apply_apply_eq_zero, add_zero, hxp]
  have hstat : Zᴴ *ᵥ (f - H *ᵥ x) = 0 := (reduced_eq_iff_stationary H f xp y).mp hy
  have hlt (v : n → 𝕜) (hv : B *ᵥ v = g) (hne : v ≠ x) :=
    quadraticObjective_lt_of_mulVec_eq_of_ne f hH h hG hstat (hv.trans hx.symm) hne
  refine ⟨x, ⟨hx, isMinOn_iff.mpr ?_⟩, ?_⟩
  · intro v hv
    by_cases he : v = x
    · exact he ▸ le_rfl
    · exact (hlt v hv he).le
  · rintro v ⟨hv, hm⟩
    by_contra hne
    exact (hlt v hv hne).not_ge (isMinOn_iff.mp hm x hx)

omit [Fintype m] in
private theorem posDef_of_unique_homogeneous_min {H : Matrix n n 𝕜} (hH : H.IsHermitian)
    (h : Function.Exact Z.mulVec B.mulVec) (hZ : Function.Injective Z.mulVec)
    (hmin : ∃! x, B *ᵥ x = 0 ∧ IsMinOn (quadraticObjective H 0) {v | B *ᵥ v = 0} x) :
    (Zᴴ * H * Z).PosDef := by
  obtain ⟨x, ⟨hx, hm⟩, hu⟩ := hmin
  have hneg : quadraticObjective H 0 (-x) = quadraticObjective H 0 x := by
    simp only [quadraticObjective, quadForm_neg_right, star_zero, zero_dotProduct, map_zero]
  have hxneg : -x = x := hu (-x) ⟨by rw [Matrix.mulVec_neg, hx, neg_zero],
    isMinOn_iff.mpr fun v hv => hneg ▸ isMinOn_iff.mp hm v hv⟩
  have hx0 : x = 0 := by
    ext i
    have hi := congrFun hxneg i
    change -(x i) = x i at hi
    have hz : (2 : 𝕜) * x i = 0 := by linear_combination -hi
    exact (mul_eq_zero.mp hz).resolve_left (by norm_num)
  subst x
  have hGH := Matrix.isHermitian_conjTranspose_mul_mul Z hH
  refine posDef_iff_quadForm_pos.mpr ⟨hGH, fun y hy => ?_⟩
  have hz : Z *ᵥ y ≠ 0 := fun he => hy (hZ (he.trans (Matrix.mulVec_zero Z).symm))
  have hfeas := h.apply_apply_eq_zero y
  have hn := isMinOn_iff.mp hm (Z *ᵥ y) hfeas
  have hstrict : quadraticObjective H 0 0 < quadraticObjective H 0 (Z *ᵥ y) := by
    refine lt_of_le_of_ne hn fun he => hz (hu _ ⟨hfeas, isMinOn_iff.mpr ?_⟩)
    intro v hv
    rw [← he]
    exact isMinOn_iff.mp hm v hv
  simp only [quadraticObjective, star_zero, zero_dotProduct, map_zero, quadForm_zero_right,
    mul_zero, sub_zero] at hstrict
  rw [← hGH.coe_re_quadForm, RCLike.ofReal_pos, quadForm_conjTranspose_mul_mul]
  linarith

/-- **Unique equality-constrained quadratic minima.** Let $\mathbf{H}$ be Hermitian and let
$\mathbf{B}$ have full row rank. For any basis $\mathbf{Z}$ of its kernel, every linear term
and every constraint right-hand side admit exactly one feasible minimizer if and only if
$\mathbf{Z}^{\mathsf{H}}\mathbf{H}\mathbf{Z}$ is positive definite. For a square invertible
constraint matrix the feasible set is a singleton and the reduced matrix has size zero.
[BenziGolubLiesen2005, §1 and §6], with the converse obtained from the homogeneous problem.
Result: kkt-reduced-hessian -/
theorem _root_.Matrix.IsHermitian.forall_existsUnique_isMinOn_quadraticObjective_iff
    {H : Matrix n n 𝕜} (hH : H.IsHermitian) (h : Function.Exact Z.mulVec B.mulVec)
    (hB : Function.Injective Bᴴ.mulVec) (hZ : Function.Injective Z.mulVec) :
    (∀ (f : n → 𝕜) (g : m → 𝕜),
      ∃! x, B *ᵥ x = g ∧ IsMinOn (quadraticObjective H f) {v | B *ᵥ v = g} x) ↔
      (Zᴴ * H * Z).PosDef := by
  exact ⟨fun hm => posDef_of_unique_homogeneous_min hH h hZ (hm 0 0),
    existsUnique_feasible_min hH h hB⟩

end NLAlib
