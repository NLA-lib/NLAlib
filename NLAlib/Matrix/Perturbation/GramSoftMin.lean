/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Functions.InversePowerSoftMin

/-!
# Coordinate derivatives of the inverse-power Gram potential

The shifted real Gram potential has explicit first and second directional coefficients.
At zero shift, inverse trace products yield the Euler identity, the gradient energy
estimate, and the finite Laplacian bound.

## Main results

* `NLAlib.gramSoftMinGradient`: its matrix gradient coefficient.
* `NLAlib.gramSoftMinLaplacian_unshifted_le`: the finite Laplacian bound.
* `NLAlib.frobInner_gramSoftMinGradient_unshifted_eq_of_pos`: the global Euler identity.
* `NLAlib.frobNorm_gramSoftMinGradient_sq_unshifted_le_of_pos`: the global energy bound.
-/

@[expose] public section

open scoped Matrix Matrix.Norms.L2Operator Topology
open Matrix Filter

namespace NLAlib

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- The Gram matrix plus a scalar multiple of the identity. -/
def regularizedGram {𝕜 : Type*} [RCLike 𝕜] (ε : ℝ) (G : Matrix ι κ 𝕜) :
    Matrix ι ι 𝕜 := G * Gᴴ + ε • 1

/-- The matrix gradient coefficient of the shifted real Gram potential. -/
noncomputable def gramSoftMinGradient (n : ℕ) (ε : ℝ) (G : Matrix ι κ ℝ) : Matrix ι κ ℝ :=
  (2 : ℝ) • (inversePowerSoftMinWeight n (regularizedGram ε G) * G)

/-- The second directional coefficient of the shifted real Gram potential. -/
noncomputable def gramSoftMinSecond (n : ℕ) (ε : ℝ) (G E : Matrix ι κ ℝ) : ℝ :=
  inversePowerSoftMinSecond n (regularizedGram ε G) (E * Gᴴ + G * Eᴴ) +
    inversePowerSoftMinFirst n (regularizedGram ε G) ((2 : ℝ) • (E * Eᴴ))

/-- The sum of second directional coefficients along all real Gram coordinate directions. -/
noncomputable def gramSoftMinLaplacian (n : ℕ) (ε : ℝ) (G : Matrix ι κ ℝ) : ℝ :=
  ∑ i, ∑ j, gramSoftMinSecond n ε G (Matrix.single i j 1)

omit [Fintype ι] [DecidableEq κ] in
/-- At zero shift, the regularized Gram matrix is the original Gram matrix. -/
theorem regularizedGram_zero {𝕜 : Type*} [RCLike 𝕜] (G : Matrix ι κ 𝕜) :
    regularizedGram 0 G = G * Gᴴ := by
  simp only [regularizedGram, zero_smul, add_zero]

omit [Fintype ι] [DecidableEq κ] in
private theorem regularizedGram_add_smul (ε t : ℝ) (G E : Matrix ι κ ℝ) :
    regularizedGram ε (G + t • E) = regularizedGram ε G +
      t • (E * Gᴴ + G * Eᴴ) + t ^ 2 • (E * Eᴴ) := by
  simp only [regularizedGram, Matrix.conjTranspose_add, Matrix.conjTranspose_smul, star_trivial,
    Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, pow_two]
  module

omit [Fintype ι] [DecidableEq κ] in
private theorem hasDerivAt_regularizedGram_add_smul [Finite ι] (ε : ℝ)
    (G E : Matrix ι κ ℝ) (t : ℝ) :
    HasDerivAt (fun x : ℝ => regularizedGram ε (G + x • E))
      (E * Gᴴ + G * Eᴴ + (2 * t) • (E * Eᴴ)) t := by
  let := Fintype.ofFinite ι
  have hlin := ((hasDerivAt_id t).smul_const (E * Gᴴ + G * Eᴴ)).const_add
    (regularizedGram ε G)
  have hquad := ((hasDerivAt_id t).pow 2).smul_const (E * Eᴴ)
  have h := hlin.add hquad
  simpa only [regularizedGram_add_smul, id_eq, Pi.add_apply, Pi.pow_apply,
    Nat.reduceSub, pow_one, mul_one, one_smul, Nat.cast_ofNat] using! h

omit [Fintype ι] [DecidableEq ι] [DecidableEq κ] in
private theorem hasDerivAt_regularizedGram_first [Finite ι] (G E : Matrix ι κ ℝ) (t : ℝ) :
    HasDerivAt (fun x : ℝ => E * Gᴴ + G * Eᴴ + (2 * x) • (E * Eᴴ))
      ((2 : ℝ) • (E * Eᴴ)) t := by
  classical
  let := Fintype.ofFinite ι
  simpa only [mul_one, id_eq] using ((hasDerivAt_id t).const_mul 2).smul_const (E * Eᴴ)
    |>.const_add (E * Gᴴ + G * Eᴴ)

omit [DecidableEq κ] in
private theorem frobInner_gramSoftMinGradient_eq_trace (n : ℕ) (ε : ℝ) (G : Matrix ι κ ℝ) :
    frobInner G (gramSoftMinGradient n ε G) =
      2 * Matrix.trace (inversePowerSoftMinWeight n (regularizedGram ε G) * (G * Gᴴ)) := by
  rw [gramSoftMinGradient, frobInner_smul_right, frobInner_eq_re_trace, RCLike.re_to_real ]
  congr 1
  calc _ = Matrix.trace ((Gᴴ * inversePowerSoftMinWeight n (regularizedGram ε G)) * G) := by
        congr 1; simp only [Matrix.mul_assoc]
    _ = Matrix.trace (G * (Gᴴ * inversePowerSoftMinWeight n (regularizedGram ε G))) := by
          simpa only [Matrix.mul_assoc] using
            (Matrix.trace_mul_cycle Gᴴ (inversePowerSoftMinWeight n (regularizedGram ε G)) G)
    _ = Matrix.trace ((G * Gᴴ) * inversePowerSoftMinWeight n (regularizedGram ε G)) := by
        congr 1; simp only [Matrix.mul_assoc]
    _ = _ := Matrix.trace_mul_comm _ _

private theorem trace_mul_gram_direction (X : Matrix ι ι ℝ) (hX : Xᴴ = X)
    (G : Matrix ι κ ℝ) (i : ι) (j : κ) :
    let E : Matrix ι κ ℝ := Matrix.single i j 1
    Matrix.trace (X * (E * Gᴴ + G * Eᴴ)) = 2 * (X * G) i j := by
  dsimp only
  let E : Matrix ι κ ℝ := Matrix.single i j 1
  have hGX : Gᴴ * X = (X * G)ᴴ := by rw [Matrix.conjTranspose_mul, hX]
  have h1 : Matrix.trace (X * (E * Gᴴ)) = (X * G) i j := by
    rw [← Matrix.mul_assoc, Matrix.trace_mul_cycle]
    simp only [E, Matrix.trace_mul_single, op_smul_eq_smul, smul_eq_mul,
      one_mul, hGX, Matrix.conjTranspose_apply, star_trivial]
  have h2 : Matrix.trace (X * (G * Eᴴ)) = (X * G) i j := by
    rw [← Matrix.mul_assoc]
    simp only [E, Matrix.conjTranspose_single, star_trivial, Matrix.trace_mul_single,
      op_smul_eq_smul, smul_eq_mul, one_mul]
  change Matrix.trace (X * (E * Gᴴ + G * Eᴴ)) = _
  rw [mul_add, Matrix.trace_add, h1, h2]
  ring

private theorem sum_trace_mul_gram_direction_sq (X : Matrix ι ι ℝ) (hX : Xᴴ = X)
    (G : Matrix ι κ ℝ) :
    (∑ i, ∑ j, let E : Matrix ι κ ℝ := Matrix.single i j 1
      Matrix.trace (X * (E * Gᴴ + G * Eᴴ)) ^ 2) =
      4 * Matrix.trace (X ^ 2 * (G * Gᴴ)) := by
  simp_rw [trace_mul_gram_direction X hX G, mul_pow]
  norm_num only
  have hfrob : frobInner (X * G) (X * G) = Matrix.trace (X ^ 2 * (G * Gᴴ)) := by
    rw [frobInner_eq_re_trace, RCLike.re_to_real,
      Matrix.conjTranspose_mul, hX, pow_two]
    calc Matrix.trace ((Gᴴ * X) * (X * G)) = Matrix.trace (Gᴴ * (X * X * G)) := by
          congr 1; simp only [Matrix.mul_assoc]
      _ = Matrix.trace ((X * X * G) * Gᴴ) := Matrix.trace_mul_comm _ _
      _ = _ := by congr 1; simp only [Matrix.mul_assoc]
  rw [← hfrob]
  simp only [frobInner_eq_sum_mul, ← Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

private theorem trace_mul_gram_direction_mul_gram_direction (X Y : Matrix ι ι ℝ)
    (hX : Xᴴ = X) (hY : Yᴴ = Y) (G : Matrix ι κ ℝ) (i : ι) (j : κ) :
    let E : Matrix ι κ ℝ := Matrix.single i j 1
    Matrix.trace (X * (E * Gᴴ + G * Eᴴ) * Y * (E * Gᴴ + G * Eᴴ)) =
      2 * (X * G) i j * (Y * G) i j + X i i * (Gᴴ * Y * G) j j +
        Y i i * (Gᴴ * X * G) j j := by
  dsimp only
  let E : Matrix ι κ ℝ := Matrix.single i j 1
  have hGX : Gᴴ * X = (X * G)ᴴ := by rw [Matrix.conjTranspose_mul, hX]
  have hGY : Gᴴ * Y = (Y * G)ᴴ := by rw [Matrix.conjTranspose_mul, hY]
  have h1 : Matrix.trace (X * (E * Gᴴ) * Y * (E * Gᴴ)) =
      (X * G) i j * (Y * G) i j := by
    calc _ = Matrix.trace (X * (E * (Gᴴ * Y) * E * Gᴴ)) := by
          congr 1; simp only [Matrix.mul_assoc]
      _ = Matrix.trace ((E * (Gᴴ * Y) * E * Gᴴ) * X) := Matrix.trace_mul_comm _ _
      _ = Matrix.trace ((E * (Gᴴ * Y) * E) * (Gᴴ * X)) := by
          congr 1; simp only [Matrix.mul_assoc]
      _ = _ := by
          simp only [E, Matrix.single_mul_mul_single, one_mul, mul_one,
            Matrix.trace_single_mul, smul_eq_mul, hGX, hGY,
            Matrix.conjTranspose_apply, star_trivial]
          ring
  have h2 : Matrix.trace (X * (E * Gᴴ) * Y * (G * Eᴴ)) =
      X i i * (Gᴴ * Y * G) j j := by
    calc _ = Matrix.trace (X * (E * (Gᴴ * Y * G) * Eᴴ)) := by
          congr 1; simp only [Matrix.mul_assoc]
      _ = _ := by
          simp only [E, Matrix.conjTranspose_single, star_trivial, Matrix.single_mul_mul_single,
            one_mul, mul_one, Matrix.trace_mul_single, op_smul_eq_smul, smul_eq_mul]
          ring
  have h3 : Matrix.trace (X * (G * Eᴴ) * Y * (E * Gᴴ)) =
      Y i i * (Gᴴ * X * G) j j := by
    calc _ = Matrix.trace ((X * G * Eᴴ * Y * E) * Gᴴ) := by
          congr 1; simp only [Matrix.mul_assoc]
      _ = Matrix.trace (Gᴴ * (X * G * Eᴴ * Y * E)) := Matrix.trace_mul_comm _ _
      _ = Matrix.trace ((Gᴴ * X * G) * (Eᴴ * Y * E)) := by
          congr 1; simp only [Matrix.mul_assoc]
      _ = _ := by
          simp only [E, Matrix.conjTranspose_single, star_trivial, Matrix.single_mul_mul_single,
            one_mul, mul_one, Matrix.trace_mul_single, op_smul_eq_smul, smul_eq_mul]
  have h4 : Matrix.trace (X * (G * Eᴴ) * Y * (G * Eᴴ)) =
      (X * G) i j * (Y * G) i j := by
    calc _ = Matrix.trace ((X * G) * (Eᴴ * (Y * G) * Eᴴ)) := by
          congr 1; simp only [Matrix.mul_assoc]
      _ = _ := by
          simp only [E, Matrix.conjTranspose_single, star_trivial, Matrix.single_mul_mul_single,
            one_mul, mul_one, Matrix.trace_mul_single, op_smul_eq_smul, smul_eq_mul]
          ring
  change Matrix.trace (X * (E * Gᴴ + G * Eᴴ) * Y * (E * Gᴴ + G * Eᴴ)) = _
  simp only [mul_add, add_mul, Matrix.trace_add]
  rw [h1, h2, h3, h4]
  ring

private theorem sum_trace_mul_gram_direction_mul_gram_direction (X Y : Matrix ι ι ℝ)
    (hX : Xᴴ = X) (hY : Yᴴ = Y) (G : Matrix ι κ ℝ) :
    (∑ i, ∑ j, let E : Matrix ι κ ℝ := Matrix.single i j 1
      Matrix.trace (X * (E * Gᴴ + G * Eᴴ) * Y * (E * Gᴴ + G * Eᴴ))) =
      2 * Matrix.trace (X * Y * (G * Gᴴ)) +
        Matrix.trace X * Matrix.trace (Y * (G * Gᴴ)) +
        Matrix.trace Y * Matrix.trace (X * (G * Gᴴ)) := by
  simp_rw [trace_mul_gram_direction_mul_gram_direction X Y hX hY G]
  have hfrob : frobInner (X * G) (Y * G) = Matrix.trace (X * Y * (G * Gᴴ)) := by
    rw [frobInner_eq_re_trace, RCLike.re_to_real,
      Matrix.conjTranspose_mul, hX]
    calc Matrix.trace ((Gᴴ * X) * (Y * G)) = Matrix.trace (Gᴴ * (X * Y * G)) := by
          congr 1; simp only [Matrix.mul_assoc]
      _ = Matrix.trace ((X * Y * G) * Gᴴ) := Matrix.trace_mul_comm _ _
      _ = _ := by congr 1; simp only [Matrix.mul_assoc]
  have htraceX : Matrix.trace (Gᴴ * X * G) = Matrix.trace (X * (G * Gᴴ)) := by
    rw [Matrix.trace_mul_cycle, ← Matrix.mul_assoc, Matrix.trace_mul_comm (G * Gᴴ) X]
    simp only [Matrix.mul_assoc]
  have htraceY : Matrix.trace (Gᴴ * Y * G) = Matrix.trace (Y * (G * Gᴴ)) := by
    rw [Matrix.trace_mul_cycle, ← Matrix.mul_assoc, Matrix.trace_mul_comm (G * Gᴴ) Y]
    simp only [Matrix.mul_assoc]
  rw [← hfrob, ← htraceX, ← htraceY]
  simp only [frobInner_eq_sum_mul, Matrix.trace, Matrix.diag, Finset.sum_add_distrib,
    Finset.mul_sum, Finset.sum_mul]
  congr 2
  · apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  all_goals rw [Finset.sum_comm]

private theorem sum_inversePowerHessianKernel_gram_direction_eq
    (R : Matrix ι ι ℝ) (hR : R.PosSemidef) (G : Matrix ι κ ℝ) (n : ℕ) :
    (∑ i, ∑ j, let E : Matrix ι κ ℝ := Matrix.single i j 1
      inversePowerHessianKernel R (E * Gᴴ + G * Eᴴ) n) =
      ∑ a ∈ Finset.range (n + 1),
        (2 * Matrix.trace (R ^ (n + 2) * (G * Gᴴ)) +
          Matrix.trace (R ^ (n - a + 1)) * Matrix.trace (R ^ (a + 1) * (G * Gᴴ)) +
          Matrix.trace (R ^ (a + 1)) * Matrix.trace (R ^ (n - a + 1) * (G * Gᴴ))) := by
  unfold inversePowerHessianKernel
  dsimp only
  calc _ = (∑ i, ∑ a ∈ Finset.range (n + 1), ∑ j,
        let E : Matrix ι κ ℝ := Matrix.single i j 1
        Matrix.trace (R ^ (n - a + 1) * (E * Gᴴ + G * Eᴴ) * R ^ (a + 1) *
          (E * Gᴴ + G * Eᴴ))) := by
          apply Finset.sum_congr rfl
          intro i _
          exact Finset.sum_comm
    _ = (∑ a ∈ Finset.range (n + 1), ∑ i, ∑ j,
        let E : Matrix ι κ ℝ := Matrix.single i j 1
        Matrix.trace (R ^ (n - a + 1) * (E * Gᴴ + G * Eᴴ) * R ^ (a + 1) *
          (E * Gᴴ + G * Eᴴ))) := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a ha
      have hX : (R ^ (n - a + 1))ᴴ = R ^ (n - a + 1) :=
        (hR.pow _).isHermitian.eq
      have hY : (R ^ (a + 1))ᴴ = R ^ (a + 1) :=
        (hR.pow _).isHermitian.eq
      rw [sum_trace_mul_gram_direction_mul_gram_direction _ _ hX hY G, ← pow_add]
      have ha' : a ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
      rw [show n - a + 1 + (a + 1) = n + 2 by omega]

private theorem gramSoftMinLaplacian_eq (n : ℕ) (ε : ℝ) (G : Matrix ι κ ℝ)
    (hpd : (regularizedGram ε G).PosDef) :
    let R := (regularizedGram ε G)⁻¹
    let T := Matrix.trace (R ^ n)
    gramSoftMinLaplacian n ε G =
      2 * Fintype.card κ * Matrix.trace (inversePowerSoftMinWeight n (regularizedGram ε G)) +
      4 * ((n : ℝ) + 1) * T ^ (-(n : ℝ)⁻¹ - 2) * Matrix.trace (R ^ (2 * n + 2) * (G * Gᴴ)) -
      T ^ (-(n : ℝ)⁻¹ - 1) *
        ∑ a ∈ Finset.range (n + 1),
          (2 * Matrix.trace (R ^ (n + 2) * (G * Gᴴ)) +
            Matrix.trace (R ^ (n - a + 1)) * Matrix.trace (R ^ (a + 1) * (G * Gᴴ)) +
            Matrix.trace (R ^ (a + 1)) * Matrix.trace (R ^ (n - a + 1) * (G * Gᴴ))) := by
  dsimp only
  let R := (regularizedGram ε G)⁻¹
  have hR : R.PosSemidef := hpd.inv.posSemidef
  have hX : (R ^ (n + 1))ᴴ = R ^ (n + 1) :=
    (hR.pow _).isHermitian.eq
  have hsq := sum_trace_mul_gram_direction_sq (R ^ (n + 1)) hX G
  rw [← pow_mul, show (n + 1) * 2 = 2 * n + 2 by omega] at hsq
  have hk := sum_inversePowerHessianKernel_gram_direction_eq R hR G n
  dsimp only [R] at hsq hk
  have hfirst : (∑ i, ∑ j, let E : Matrix ι κ ℝ := Matrix.single i j 1
      inversePowerSoftMinFirst n (regularizedGram ε G) ((2 : ℝ) • (E * Eᴴ))) =
      2 * Fintype.card κ * Matrix.trace (inversePowerSoftMinWeight n (regularizedGram ε G)) := by
    simp only [inversePowerSoftMinFirst, Matrix.conjTranspose_single, star_trivial,
      Matrix.single_mul_single_same, one_mul, Matrix.mul_smul, Matrix.trace_smul,
      smul_eq_mul, Matrix.trace_mul_single, op_smul_eq_smul, one_mul]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Matrix.trace, Matrix.diag]
    rw [← Finset.mul_sum, ← Finset.mul_sum]
    ring
  unfold gramSoftMinLaplacian gramSoftMinSecond
  simp only [Finset.sum_add_distrib]
  rw [hfirst]
  unfold inversePowerSoftMinSecond
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [hsq, hk]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

private lemma sum_trace_power_reflect (S : ℕ → ℝ) (n : ℕ) :
    (∑ a ∈ Finset.range (n + 1), S (n - a + 1) * S a) =
      ∑ a ∈ Finset.range (n + 1), S (a + 1) * S (n - a) := by
  have href := Finset.sum_range_reflect (fun a => S (a + 1) * S (n - a)) (n + 1)
  apply Eq.trans ?_ href
  apply Finset.sum_congr rfl
  intro a ha
  have ha' : a ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
  simp only [Nat.add_sub_cancel]
  rw [show n - (n - a) = a by omega]

omit [DecidableEq κ] in
private theorem trace_inv_gram_pow_succ_mul_gram (G : Matrix ι κ ℝ)
    (hpd : (G * Gᴴ).PosDef) (a : ℕ) :
    Matrix.trace ((G * Gᴴ)⁻¹ ^ (a + 1) * (G * Gᴴ)) =
      Matrix.trace ((G * Gᴴ)⁻¹ ^ a) := by
  rw [pow_succ, Matrix.mul_assoc,
    Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hpd.isUnit), Matrix.mul_one]

/-- For a real matrix $\mathbf{G}$ on a nonempty row
type with positive definite Gram matrix, the unshifted inverse-power Laplacian equals its
dimension term minus two trace-product defects. -/
theorem gramSoftMinLaplacian_unshifted_eq [Nonempty ι]
    (n : ℕ) (G : Matrix ι κ ℝ) (hpd : (G * Gᴴ).PosDef) :
    gramSoftMinLaplacian n 0 G =
      (let R := (G * Gᴴ)⁻¹
       let S := fun a : ℕ => Matrix.trace (R ^ a)
       let c := S n ^ (-(n : ℝ)⁻¹ - 1)
       2 * ((Fintype.card κ : ℝ) - Fintype.card ι + 1) * c * S (n + 1) -
         4 * ((n : ℝ) + 1) * c * (S (n + 1) - S (2 * n + 1) / S n) -
         2 * c * ∑ a ∈ Finset.range n, (S (a + 1) * S (n - a) - S (n + 1))) := by
  dsimp only
  let R := (G * Gᴴ)⁻¹
  let S := fun a : ℕ => Matrix.trace (R ^ a)
  have hT : 0 < S n := hpd.inv.trace_pow_pos n
  have hreg : (regularizedGram 0 G).PosDef := by simpa only [regularizedGram_zero] using hpd
  have h := gramSoftMinLaplacian_eq n 0 G hreg
  dsimp only at h
  simp only [regularizedGram_zero] at h
  have htrace (a : ℕ) : Matrix.trace (R ^ (a + 1) * (G * Gᴴ)) = S a :=
    trace_inv_gram_pow_succ_mul_gram G hpd a
  change gramSoftMinLaplacian n 0 G =
    2 * Fintype.card κ * Matrix.trace (inversePowerSoftMinWeight n (G * Gᴴ)) +
      4 * ((n : ℝ) + 1) * S n ^ (-(n : ℝ)⁻¹ - 2) *
        Matrix.trace (R ^ (2 * n + 2) * (G * Gᴴ)) -
      S n ^ (-(n : ℝ)⁻¹ - 1) *
        ∑ a ∈ Finset.range (n + 1), (2 * Matrix.trace (R ^ (n + 2) * (G * Gᴴ)) +
          S (n - a + 1) * Matrix.trace (R ^ (a + 1) * (G * Gᴴ)) +
          S (a + 1) * Matrix.trace (R ^ (n - a + 1) * (G * Gᴴ))) at h
  rw [show 2 * n + 2 = (2 * n + 1) + 1 by omega, htrace,
    show n + 2 = (n + 1) + 1 by omega, htrace] at h
  simp_rw [htrace] at h
  have hweight : Matrix.trace (inversePowerSoftMinWeight n (G * Gᴴ)) =
      S n ^ (-(n : ℝ)⁻¹ - 1) * S (n + 1) := by
    rw [inversePowerSoftMinWeight, Matrix.trace_smul, smul_eq_mul]
  rw [hweight] at h
  have hpower : S n ^ (-(n : ℝ)⁻¹ - 2) = S n ^ (-(n : ℝ)⁻¹ - 1) / S n := by
    rw [show -(n : ℝ)⁻¹ - 2 = (-(n : ℝ)⁻¹ - 1) - 1 by ring,
      Real.rpow_sub_one hT.ne']
  rw [hpower] at h
  simp only [Finset.sum_add_distrib] at h
  rw [sum_trace_power_reflect S n] at h
  have hSzero : S 0 = Fintype.card ι := by simp [S]
  have hsplit : (∑ a ∈ Finset.range (n + 1), S (a + 1) * S (n - a)) =
      (∑ a ∈ Finset.range n, S (a + 1) * S (n - a)) + S (n + 1) * Fintype.card ι := by
    rw [Finset.sum_range_succ, Nat.sub_self, hSzero]
  rw [hsplit] at h
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one] at h
  rw [h]
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  ring

/-- **Finite inverse-power Gram Laplacian bound.**
For a real matrix $\mathbf{G}$ with a nonempty row type of size $r$, column type of size $k$,
and positive definite Gram matrix, every positive inverse power has Laplacian at most
$2(k-r+1)$ since positive definiteness forces $r \le k$.
No printed source. Original NLAlib atlas proof at
`77514ce42a0e437d837797a063ac161f41022730`.
Result: inverse-power-gram-laplacian -/
theorem gramSoftMinLaplacian_unshifted_le [Nonempty ι] (n : ℕ) (hn : 0 < n)
    (G : Matrix ι κ ℝ) (hpd : (G * Gᴴ).PosDef) :
    gramSoftMinLaplacian n 0 G ≤ 2 * ((Fintype.card κ : ℝ) - Fintype.card ι + 1) := by
  have hrows : Fintype.card ι ≤ Fintype.card κ := by
    rw [← Matrix.rank_of_isUnit (G * Gᴴ) hpd.isUnit]
    exact (Matrix.rank_mul_le_left G Gᴴ).trans G.rank_le_card_width
  have hgap : 0 ≤ (Fintype.card κ : ℝ) - Fintype.card ι + 1 := by
    have : (Fintype.card ι : ℝ) ≤ Fintype.card κ := by exact_mod_cast hrows
    linarith
  let R := (G * Gᴴ)⁻¹
  let S := fun a : ℕ => Matrix.trace (R ^ a)
  let c := S n ^ (-(n : ℝ)⁻¹ - 1)
  have hT : 0 < S n := hpd.inv.trace_pow_pos n
  have hc : 0 ≤ c := Real.rpow_nonneg hT.le _
  have hmain : c * S (n + 1) ≤ 1 := by
    simpa only [c, S, R, inversePowerSoftMinWeight, Matrix.trace_smul, smul_eq_mul] using
      trace_inversePowerSoftMinWeight_le_one n hn hpd
  have hprod : S (2 * n + 1) ≤ S n * S (n + 1) := by
    simpa only [RCLike.re_to_real, show n + (n + 1) = 2 * n + 1 by omega] using
      hpd.inv.posSemidef.re_trace_pow_add_le_mul n (n + 1)
  have hbracket : 0 ≤ S (n + 1) - S (2 * n + 1) / S n := by
    have hdiv : S (2 * n + 1) / S n ≤ S (n + 1) :=
      (div_le_iff₀ hT).2 (by simpa only [mul_comm] using hprod)
    linarith
  have hsum : 0 ≤ ∑ a ∈ Finset.range n, (S (a + 1) * S (n - a) - S (n + 1)) := by
    apply Finset.sum_nonneg
    intro a ha
    have ha' : a < n := Finset.mem_range.mp ha
    have h := hpd.inv.posSemidef.re_trace_pow_add_le_mul (a + 1) (n - a)
    have he : a + 1 + (n - a) = n + 1 := by omega
    rw [he] at h
    exact sub_nonneg.mpr (by simpa only [RCLike.re_to_real] using h)
  have heq := gramSoftMinLaplacian_unshifted_eq n G hpd
  change gramSoftMinLaplacian n 0 G =
    2 * ((Fintype.card κ : ℝ) - Fintype.card ι + 1) * c * S (n + 1) -
      4 * ((n : ℝ) + 1) * c * (S (n + 1) - S (2 * n + 1) / S n) -
      2 * c * ∑ a ∈ Finset.range n, (S (a + 1) * S (n - a) - S (n + 1)) at heq
  rw [heq]
  calc _ ≤ 2 * ((Fintype.card κ : ℝ) - Fintype.card ι + 1) * c * S (n + 1) := by
        have h1 : 0 ≤ 4 * ((n : ℝ) + 1) * c * (S (n + 1) - S (2 * n + 1) / S n) := by positivity
        have h2 : 0 ≤ 2 * c * ∑ a ∈ Finset.range n,
            (S (a + 1) * S (n - a) - S (n + 1)) := by positivity
        linarith
    _ ≤ _ := by
        have h := mul_le_mul_of_nonneg_left hmain (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hgap)
        simpa only [mul_one, mul_assoc] using h

omit [DecidableEq κ] in
private theorem frobInner_gramSoftMinGradient_unshifted_eq [Nonempty ι]
    (n : ℕ) (G : Matrix ι κ ℝ) (hpd : (G * Gᴴ).PosDef) :
    frobInner G (gramSoftMinGradient n 0 G) = 2 * inversePowerSoftMin n (G * Gᴴ) := by
  have hT : 0 < Matrix.trace ((G * Gᴴ)⁻¹ ^ n) := hpd.inv.trace_pow_pos n
  rw [frobInner_gramSoftMinGradient_eq_trace, regularizedGram_zero,
    inversePowerSoftMinWeight, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul,
    trace_inv_gram_pow_succ_mul_gram G hpd n]
  congr 1
  nth_rw 2 [← Real.rpow_one (Matrix.trace ((G * Gᴴ)⁻¹ ^ n))]
  rw [← Real.rpow_add hT]
  congr 1
  ring

omit [DecidableEq κ] in
private theorem frobNorm_gramSoftMinGradient_sq_eq_trace (n : ℕ) (ε : ℝ) (G : Matrix ι κ ℝ)
    (hpd : (regularizedGram ε G).PosDef) :
    frobNorm (gramSoftMinGradient n ε G) ^ 2 = 4 *
      Matrix.trace (inversePowerSoftMinWeight n (regularizedGram ε G) ^ 2 * (G * Gᴴ)) := by
  have hP : (inversePowerSoftMinWeight n (regularizedGram ε G))ᴴ =
      inversePowerSoftMinWeight n (regularizedGram ε G) :=
    (inversePowerSoftMinWeight_posSemidef n hpd.posSemidef).isHermitian.eq
  rw [gramSoftMinGradient, frobNorm_smul, mul_pow, frobNorm_sq_eq_re_trace]
  norm_num only [Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  congr 1
  rw [RCLike.re_to_real,
      Matrix.conjTranspose_mul, hP, pow_two]
  calc _ = Matrix.trace (Gᴴ * (inversePowerSoftMinWeight n (regularizedGram ε G) *
        inversePowerSoftMinWeight n (regularizedGram ε G) * G)) := by
        congr 1; simp only [Matrix.mul_assoc]
    _ = Matrix.trace ((inversePowerSoftMinWeight n (regularizedGram ε G) *
        inversePowerSoftMinWeight n (regularizedGram ε G) * G) * Gᴴ) := Matrix.trace_mul_comm _ _
    _ = _ := by congr 1; simp only [Matrix.mul_assoc]

omit [DecidableEq κ] in
/-- At a positive definite real Gram matrix,
the unshifted gradient energy equals four times the trace of the inverse Gram power $2n+1$
times the square of the inverse-power weight coefficient. -/
theorem frobNorm_gramSoftMinGradient_sq_unshifted_eq (n : ℕ)
    (G : Matrix ι κ ℝ) (hpd : (G * Gᴴ).PosDef) :
    frobNorm (gramSoftMinGradient n 0 G) ^ 2 =
      (let R := (G * Gᴴ)⁻¹
       let c := Matrix.trace (R ^ n) ^ (-(n : ℝ)⁻¹ - 1)
       4 * c ^ 2 * Matrix.trace (R ^ (2 * n + 1))) := by
  have hreg : (regularizedGram 0 G).PosDef := by simpa only [regularizedGram_zero] using hpd
  have h := frobNorm_gramSoftMinGradient_sq_eq_trace n 0 G hreg
  simp only [regularizedGram_zero] at h
  rw [inversePowerSoftMinWeight, smul_pow, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul,
    ← pow_mul, show (n + 1) * 2 = (2 * n + 1) + 1 by omega,
    trace_inv_gram_pow_succ_mul_gram G hpd] at h
  simpa only [mul_assoc] using h

omit [DecidableEq κ] in
private theorem frobNorm_gramSoftMinGradient_sq_unshifted_le [Nonempty ι]
    (n : ℕ) (hn : 0 < n) (G : Matrix ι κ ℝ) (hpd : (G * Gᴴ).PosDef) :
    frobNorm (gramSoftMinGradient n 0 G) ^ 2 ≤ 4 * inversePowerSoftMin n (G * Gᴴ) := by
  let R := (G * Gᴴ)⁻¹
  let S := fun a : ℕ => Matrix.trace (R ^ a)
  let c := S n ^ (-(n : ℝ)⁻¹ - 1)
  have hT : 0 < S n := hpd.inv.trace_pow_pos n
  have hPhi : c * S n = inversePowerSoftMin n (G * Gᴴ) := by
    dsimp only [c, inversePowerSoftMin, S, R]
    nth_rw 2 [← Real.rpow_one (Matrix.trace ((G * Gᴴ)⁻¹ ^ n))]
    rw [← Real.rpow_add hT]
    congr 1; ring
  have hmain : c * S (n + 1) ≤ 1 := by
    simpa only [c, S, R, inversePowerSoftMinWeight, Matrix.trace_smul, smul_eq_mul] using
      trace_inversePowerSoftMinWeight_le_one n hn hpd
  have hprod : S (2 * n + 1) ≤ S n * S (n + 1) := by
    simpa only [RCLike.re_to_real, show n + (n + 1) = 2 * n + 1 by omega] using
      hpd.inv.posSemidef.re_trace_pow_add_le_mul n (n + 1)
  calc frobNorm (gramSoftMinGradient n 0 G) ^ 2 = 4 * c ^ 2 * S (2 * n + 1) :=
        frobNorm_gramSoftMinGradient_sq_unshifted_eq n G hpd
    _ ≤ 4 * c ^ 2 * (S n * S (n + 1)) :=
        mul_le_mul_of_nonneg_left hprod (by positivity)
    _ = 4 * inversePowerSoftMin n (G * Gᴴ) * (c * S (n + 1)) := by rw [← hPhi]; ring
    _ ≤ 4 * inversePowerSoftMin n (G * Gᴴ) := by
        have hnn : 0 ≤ inversePowerSoftMin n (G * Gᴴ) := Real.rpow_nonneg hT.le _
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hmain (by positivity)

omit [DecidableEq κ] in
private theorem inv_gram_eq_zero_of_not_posDef (G : Matrix ι κ ℝ)
    (hnot : ¬(G * Gᴴ).PosDef) : (G * Gᴴ)⁻¹ = 0 := by
  have hPSD : (G * Gᴴ).PosSemidef := Matrix.posSemidef_self_mul_conjTranspose G
  have hnotunit : ¬IsUnit (G * Gᴴ) := fun hunit => hnot ((hPSD.posDef_iff_isUnit).2 hunit)
  have hnotdet : ¬IsUnit (G * Gᴴ).det := fun hdet =>
    hnotunit ((Matrix.isUnit_iff_isUnit_det _).2 hdet)
  exact Matrix.nonsing_inv_apply_not_isUnit _ hnotdet

omit [DecidableEq κ] in
/-- For a positive inverse power, the
unshifted real Gram potential vanishes when the Gram matrix is singular. -/
theorem inversePowerSoftMin_mul_conjTranspose_self_eq_zero_of_not_posDef (n : ℕ) (hn : 0 < n)
    (G : Matrix ι κ ℝ) (hnot : ¬(G * Gᴴ).PosDef) :
    inversePowerSoftMin n (G * Gᴴ) = 0 := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [inversePowerSoftMin, inv_gram_eq_zero_of_not_posDef G hnot,
    zero_pow hn.ne', Matrix.trace_zero, Real.zero_rpow (neg_ne_zero.mpr (inv_ne_zero hn0))]

omit [DecidableEq κ] in
private theorem gramSoftMinGradient_unshifted_eq_zero_of_not_posDef (n : ℕ)
    (G : Matrix ι κ ℝ) (hnot : ¬(G * Gᴴ).PosDef) : gramSoftMinGradient n 0 G = 0 := by
  rw [gramSoftMinGradient, regularizedGram_zero, inversePowerSoftMinWeight,
    inv_gram_eq_zero_of_not_posDef G hnot, zero_pow (Nat.succ_ne_zero n),
    smul_zero, Matrix.zero_mul, smul_zero]

omit [DecidableEq κ] in
/-- **Euler identity for the unshifted Gram
potential.** For a real matrix $\mathbf{G}$ on a nonempty row type and a positive inverse power,
the Frobenius pairing of $\mathbf{G}$ with its unshifted gradient coefficient is twice the
potential at $\mathbf{G}\mathbf{G}^{\mathsf{T}}$. The identity includes singular Gram matrices
under the total inverse convention.
No printed source. Original NLAlib atlas proof at
`77514ce42a0e437d837797a063ac161f41022730`.
Result: inverse-power-gram-euler -/
theorem frobInner_gramSoftMinGradient_unshifted_eq_of_pos [Nonempty ι]
    (n : ℕ) (hn : 0 < n) (G : Matrix ι κ ℝ) :
    frobInner G (gramSoftMinGradient n 0 G) = 2 * inversePowerSoftMin n (G * Gᴴ) := by
  by_cases hpd : (G * Gᴴ).PosDef
  · exact frobInner_gramSoftMinGradient_unshifted_eq n G hpd
  · rw [gramSoftMinGradient_unshifted_eq_zero_of_not_posDef n G hpd,
      inversePowerSoftMin_mul_conjTranspose_self_eq_zero_of_not_posDef n hn G hpd,
      frobInner_zero_right, mul_zero]

omit [DecidableEq κ] in
/-- **Unshifted Gram gradient energy.**
For a real matrix $\mathbf{G}$ on a nonempty row type and a positive inverse power, the squared
Frobenius norm of the unshifted gradient coefficient is at most four times the potential
at $\mathbf{G}\mathbf{G}^{\mathsf{T}}$. The bound includes singular Gram matrices.
No printed source. Original NLAlib atlas proof at
`77514ce42a0e437d837797a063ac161f41022730`.
Result: inverse-power-gram-gradient-energy -/
theorem frobNorm_gramSoftMinGradient_sq_unshifted_le_of_pos [Nonempty ι]
    (n : ℕ) (hn : 0 < n) (G : Matrix ι κ ℝ) :
    frobNorm (gramSoftMinGradient n 0 G) ^ 2 ≤ 4 * inversePowerSoftMin n (G * Gᴴ) := by
  by_cases hpd : (G * Gᴴ).PosDef
  · exact frobNorm_gramSoftMinGradient_sq_unshifted_le n hn G hpd
  · rw [gramSoftMinGradient_unshifted_eq_zero_of_not_posDef n G hpd,
      inversePowerSoftMin_mul_conjTranspose_self_eq_zero_of_not_posDef n hn G hpd, frobNorm_zero,
      zero_pow two_ne_zero, mul_zero]

private theorem inversePowerSoftMinFirst_unshifted_gram_single_eq_gradient (n : ℕ)
    (G : Matrix ι κ ℝ) (i : ι) (j : κ) (t : ℝ) :
    let E : Matrix ι κ ℝ := Matrix.single i j 1
    inversePowerSoftMinFirst n (regularizedGram 0 (G + t • E))
      (E * Gᴴ + G * Eᴴ + (2 * t) • (E * Eᴴ)) = gramSoftMinGradient n 0 (G + t • E) i j := by
  dsimp only
  let E : Matrix ι κ ℝ := Matrix.single i j 1
  have hD : E * Gᴴ + G * Eᴴ + (2 * t) • (E * Eᴴ) =
      E * (G + t • E)ᴴ + (G + t • E) * Eᴴ := by
    simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, star_trivial, Matrix.mul_add,
      Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]
    module
  have hPSD : (regularizedGram 0 (G + t • E)).PosSemidef := by
    rw [regularizedGram_zero]
    exact Matrix.posSemidef_self_mul_conjTranspose (G + t • E)
  have hP : (inversePowerSoftMinWeight n (regularizedGram 0 (G + t • E)))ᴴ =
      inversePowerSoftMinWeight n (regularizedGram 0 (G + t • E)) :=
    (inversePowerSoftMinWeight_posSemidef n hPSD).isHermitian.eq
  change inversePowerSoftMinFirst n (regularizedGram 0 (G + t • E))
      (E * Gᴴ + G * Eᴴ + (2 * t) • (E * Eᴴ)) = _
  rw [hD, inversePowerSoftMinFirst, trace_mul_gram_direction _ hP]
  rfl

/-- At a positive definite real Gram matrix
on a nonempty row type, the positive inverse-power potential has its gradient entry as
the actual coordinate derivative. -/
theorem hasDerivAt_gramSoftMin_unshifted_single [Nonempty ι]
    (n : ℕ) (hn : 0 < n) (G : Matrix ι κ ℝ) (i : ι) (j : κ) (t : ℝ)
    (hpd : (regularizedGram 0 (G + t • Matrix.single i j 1)).PosDef) :
    HasDerivAt (fun x : ℝ => inversePowerSoftMin n
      ((G + x • Matrix.single i j 1) * (G + x • Matrix.single i j 1)ᴴ))
      (gramSoftMinGradient n 0 (G + t • Matrix.single i j 1) i j) t := by
  let E : Matrix ι κ ℝ := Matrix.single i j 1
  have hA := hasDerivAt_regularizedGram_add_smul 0 G E t
  have h := hasDerivAt_inversePowerSoftMin n hn hA hpd.isUnit (hpd.inv.trace_pow_pos n)
  rw [inversePowerSoftMinFirst_unshifted_gram_single_eq_gradient] at h
  simpa only [regularizedGram_zero] using h

/-- At a positive definite real Gram
matrix on a nonempty row type, each gradient entry has its second directional coefficient as
the actual derivative in that same coordinate, for a positive inverse power. -/
theorem hasDerivAt_gramSoftMinGradient_unshifted_single_zero [Nonempty ι]
    (n : ℕ) (hn : 0 < n) (G : Matrix ι κ ℝ) (hpd : (G * Gᴴ).PosDef) (i : ι) (j : κ) :
    HasDerivAt (fun x : ℝ => gramSoftMinGradient n 0 (G + x • Matrix.single i j 1) i j)
      (gramSoftMinSecond n 0 G (Matrix.single i j 1)) 0 := by
  let E : Matrix ι κ ℝ := Matrix.single i j 1
  have hA := hasDerivAt_regularizedGram_add_smul 0 G E 0
  have hD := hasDerivAt_regularizedGram_first G E 0
  have hreg : (regularizedGram 0 G).PosDef := by simpa only [regularizedGram_zero] using hpd
  have h := hasDerivAt_inversePowerSoftMinFirst n hn hA hD
    (by simpa only [zero_smul, add_zero] using hreg.isUnit)
    (by simpa only [zero_smul, add_zero] using hreg.inv.trace_pow_pos n)
  have heq : (fun t : ℝ => inversePowerSoftMinFirst n (regularizedGram 0 (G + t • E))
      (E * Gᴴ + G * Eᴴ + (2 * t) • (E * Eᴴ))) =
      (fun t : ℝ => gramSoftMinGradient n 0 (G + t • E) i j) := by
    funext t
    exact inversePowerSoftMinFirst_unshifted_gram_single_eq_gradient n G i j t
  rw [heq] at h
  simpa only [mul_zero, zero_smul, add_zero, gramSoftMinSecond] using h

/-- At a positive definite real Gram matrix with nonempty row type, the Laplacian of the
unshifted positive inverse-power potential is the sum of its actual second derivatives along
the coordinate lines through the matrix. -/
theorem gramSoftMinLaplacian_unshifted_eq_sum_deriv_deriv [Nonempty ι]
    (n : ℕ) (hn : 0 < n) (G : Matrix ι κ ℝ) (hpd : (G * Gᴴ).PosDef) :
    gramSoftMinLaplacian n 0 G = ∑ i, ∑ j,
      deriv (deriv (fun x : ℝ => inversePowerSoftMin n ((G + x • Matrix.single i j 1) *
        (G + x • Matrix.single i j 1)ᴴ))) 0 := by
  unfold gramSoftMinLaplacian
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  let E : Matrix ι κ ℝ := Matrix.single i j 1
  let H := fun t : ℝ => G + t • E
  let A := fun t : ℝ => H t * (H t)ᴴ
  have hH : Continuous H := continuous_const.add (continuous_id.smul continuous_const)
  have hc : Continuous fun t => (A t).det :=
    (hH.matrix_mul hH.matrix_conjTranspose).matrix_det
  have h0 : (A 0).det ≠ 0 := by
    simpa only [A, H, zero_smul, add_zero] using hpd.det_pos.ne'
  have hunit : ∀ᶠ t in 𝓝 (0 : ℝ), IsUnit (A t) := by
    filter_upwards [hc.continuousAt.eventually_ne h0] with t ht
    exact (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr ht)
  have heq : deriv (fun t => inversePowerSoftMin n (A t)) =ᶠ[𝓝 (0 : ℝ)]
      fun t => gramSoftMinGradient n 0 (H t) i j := by
    filter_upwards [hunit] with t ht
    have hp : (regularizedGram 0 (H t)).PosDef := by
      rw [regularizedGram_zero]
      exact (Matrix.posSemidef_self_mul_conjTranspose (H t)).posDef_iff_isUnit.mpr ht
    exact (hasDerivAt_gramSoftMin_unshifted_single n hn G i j t hp).deriv
  have hD := hasDerivAt_gramSoftMinGradient_unshifted_single_zero n hn G hpd i j
  exact (hD.congr_of_eventuallyEq heq).deriv.symm

end NLAlib
